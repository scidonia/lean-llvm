/-
The record's `pre` at the pages' and the peel's call vectors.

`JsonS1BlocksFinalAt` reads the calling escape unit's post at the pages' and the
peel's own argument vectors, but takes the record's `pre` at those vectors as an
input (`unitPostAt_of_pre`, `peel_unitPostAt_of_pre`, `tail_calling_at_of_pre`).
The caller there is the block unit, and its staging (`S1BlocksPreAt`) plus the
chain's frame already state most of what the record asks: the block's window, the
four regions' separations and the window's read-out.  What the staging cannot
state is the *carried* part — the three mask words, the carry pair, the count's
own domain bound and the stream's capacity at the count — because those are the
page's and the peel's classifier words, the pair the previous call left, and the
run's cursor.

This module derives the record's `pre` from that carried state:

* **`controlWord_eq_specControl`** — the escape call's control mask, as the
  emission computes it (one `icmp ult <64 x i8>` against `splat 32`, packed to a
  word), is the classifier's `specControl64`.  The mask unit's `s1_control_eq`
  states that word at its `controlLanes`; this is the same packing at a joined
  byte view, so it serves both the page's `%or.i379` (`ifThen96Mask`) and the
  peel's `%or.i467` (`ifThen150QuoteWord`).
* **`page_masks`** — the page's three mask words are `specBackslash64`,
  `specControl64` and `specInString64` at the block's halves and the
  classifier's carry.  The backslash and control words are carry-free, so their
  halves are the block's; the in-string word is `PageCarry`'s two state words and
  seed lane through `fb54_xorI_eq_specInString`.
* **`carryPair_staging`, `carryPair_step`, `classCarryAt_docBlock_succ`** — the
  carry pair.  The caller's staged all-false pair is the pair the first block is
  entered with, a page's own call leaves the successor block's pair
  (`EscapeReach`'s pair word, whose parity is the classifier step's own), and the
  successor classifier carry is `carry64` at the block.  So the pair the record
  reads at a page is the classifier's carry, and its threading along the pages is
  a step, not a fresh obligation.
* **`escapePre_at`** — the record's `pre` at one call: the whole existential from
  the staging, the frame, the block's window, the count's slot, the three mask
  words and the pair.
* **`page_pre`, `peel_pre`** — at the page's and the peel's own vectors and
  memories.
* **`page_unitPostAt`, `peel_unitPostAt`, `tail_calling_of_peelPre`** — the
  committed compositions (`JsonS1BlocksUnitPost.unitPostAt_of_pre`,
  `peel_unitPostAt_of_pre`, `JsonS1BlocksFinalAt.tail_calling_at_of_pre`) at the
  derived `pre`.

## What remains

The record's `pre` asks for three things the block's own staging does not stage,
and they are inputs here rather than conclusions:

* **the carry pair.**  The slot holds what the previous call stored, and the
  chain (`CallChain`) records the frame, not the pair.  `carryPair_staging` is
  the first block's pair and `carryPair_step` the step; the induction that would
  carry the pair beside `FrameCarry` is the run's lane.
* **the count's domain bound.**  The unit sign-extends the count into an address,
  so `pre` requires the value its slot holds to be below `2 ^ 63`.  The staging
  bounds the caller's count (`xn < 2 ^ 63`) and the block count
  (`blocks * 64 + 63 < 2 ^ 32`), which is a bound below `2 ^ 64`
  (`JsonS1BlocksUnitPost.count_lt_two_pow`) and not below `2 ^ 63`; a caller that
  stages a count near `2 ^ 63` reaches a page the record refuses.
* **the stream's capacity at the page's count.**  `pre` claims presence to
  `4 * blockMax` of the count the slot holds, and presence survives only writes:
  the chain's frame is silent about the stream's own region, so the fact that has
  to carry it is the previous call's post (`HasBytes` at `blockMax` of *its*
  count), which the frame widens to the staged capacity.  At one call, without
  the previous post, the fact is an input.

None of the three is a statement about the windows or the masks, and the
accumulator's fold is `JsonS1BlocksAccFold`'s, untouched here.
-/
import LeanLLVM.Refinement.JsonS1BlocksFinalAt
import LeanLLVM.Refinement.JsonS1BlocksPageModel
import LeanLLVM.Refinement.JsonS1BlocksPeelWord

namespace LeanLLVM.Refinement.JsonS1BlocksPagePre

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksRunFrame
open LeanLLVM.Refinement.JsonS1BlocksFinal
open LeanLLVM.Refinement.JsonS1BlocksUnitPost
open LeanLLVM.Refinement.JsonS1BlocksFinalAt
open LeanLLVM.Refinement.JsonS1BlocksPeelWord
open LeanLLVM.Refinement.JsonS1BlocksPageModel
open LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The block, in the record's spelling

The record reads the block at `base + blockAddr blk0` and compares it with the
two halves' `block64`.  `docBlock` is the same sixty-four bytes at the emitted
run's own windows. -/

/-- Two takes of a list are one take: `l.take n ++ (l.drop n).take m` is the
first `n + m` bytes. -/
theorem take_append_drop_take {α : Type} (l : List α) (n m : Nat) :
    l.take n ++ (l.drop n).take m = l.take (n + m) := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
            show n + 1 + m = (n + m) + 1 from by omega, List.take_succ_cons]
          exact congrArg (List.cons x) (ih n)

/-- **The block's halves are the document's block.**  `block64` is the two
thirty-two-byte halves joined, which is `docBlock`'s own sixty-four-byte read. -/
theorem block64_blockLo_blockHi (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) :
    block64 (blockLo (padded bs) i) (blockHi (padded bs) i) = docBlock bs i := by
  unfold block64 docBlock
  rw [← take32_blockLo bs hi, ← take32_blockHi bs hi, ← List.drop_drop]
  exact take_append_drop_take _ _ _

/-! ### The control mask

The page's `%or.i379` and the peel's `%or.i467` are one comparison over the
joined byte view of the two loaded halves, packed by `bitcastMask`.  The mask
unit's `controlLanes` is the same comparison at its own halves, and
`s1_control_eq` states its packed word as `specMask64 IsControlB`. -/

/-- **The escape call's control mask is the classifier's.**  One
`icmp ult <64 x i8>` against `splat 32` over a byte view that is the block's
`blockLanes`, packed, is `specControl64`. -/
theorem controlWord_eq_specControl {k : Ctx} {join : List (BitVec 64)}
    (hjb : bitcastVecLanes 8 64 join = blockLanes k) :
    BitVec.ofNat 64 (lanesToNat
      (icmpLanes .ult (bitcastVecLanes 8 64 join) (List.replicate 64 0x20#8))) =
      specControl64 k.lo k.hi k.st := by
  rw [hjb]
  exact (s1_control_eq k).trans (specControl64_eq k).symm

/-- **The page's control mask.**  `%or.i379` at the page's two loaded halves. -/
theorem ifThen96Mask_eq_specControl {k : Ctx} {c : FusedCarry}
    {bs73 bs74 : List UInt8}
    (h73 : bs73 = List.ofFn k.lo) (h74 : bs74 = List.ofFn k.hi) :
    ifThen96Mask (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74 =
      specControl64 k.lo k.hi k.st :=
  controlWord_eq_specControl (fb54_joinBytes_eq_blockLanes k bs73 bs74 h73 h74)

/-- **The peel's control mask.**  `%or.i467` at the peel's two loaded halves. -/
theorem ifThen150QuoteWord_eq_specControl {k : Ctx} {w136 w137 : List (BitVec 64)}
    (hjb : bitcastVecLanes 8 64 (w136 ++ w137) = blockLanes k) :
    ifThen150QuoteWord w136 w137 = specControl64 k.lo k.hi k.st :=
  controlWord_eq_specControl hjb

/-! ### The page's three words at the classifier's carry

`PageCarry` states the page's carried state words; these are the page's three
argument words at the classifier's own `Ctx`.  The backslash and control words
read the block's halves alone; the in-string word reads the seed lane and the
escaped-quote conjunction through the page's own quote word. -/

/-- **The page's three mask words are the specification's.** -/
theorem page_masks (bs : List UInt8) (c : FusedCarry) (bs73 bs74 : List UInt8)
    (hi : c.i.toNat < blocksOf bs.length)
    (hcarry : PageCarry bs c)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32) :
    (fusedValues c bs73 bs74).or14 =
        specBackslash64 (blockLo (padded bs) c.i.toNat)
          (blockHi (padded bs) c.i.toNat)
          (classCarryAt (padded bs) ⟨false, false⟩ (64 * c.i.toNat)) ∧
      (ifThen96Mask (fusedValues c bs73 bs74).w73
          (fusedValues c bs73 bs74).w74 =
        specControl64 (blockLo (padded bs) c.i.toNat)
          (blockHi (padded bs) c.i.toNat)
          (classCarryAt (padded bs) ⟨false, false⟩ (64 * c.i.toNat))) ∧
      ((fusedValues c bs73 bs74).xorI =
        specInString64 (blockLo (padded bs) c.i.toNat)
          (blockHi (padded bs) c.i.toNat)
          (classCarryAt (padded bs) ⟨false, false⟩ (64 * c.i.toNat))) := by
  have h73' : bs73 = List.ofFn (pageCtx bs c.i.toNat).lo := by
    rw [h73, docBlock_take32, take32_blockLo bs hi]
    rfl
  have h74' : bs74 = List.ofFn (pageCtx bs c.i.toNat).hi := by
    rw [h74, docBlock_drop32, take32_blockHi bs hi]
    rfl
  have hklo : (pageCtx bs c.i.toNat).lo = blockLo (padded bs) c.i.toNat := rfl
  have hkhi : (pageCtx bs c.i.toNat).hi = blockHi (padded bs) c.i.toNat := rfl
  have hkst : (pageCtx bs c.i.toNat).st =
      classCarryAt (padded bs) ⟨false, false⟩ (64 * c.i.toNat) := rfl
  have hst : (pageCtx bs c.i.toNat).st.oddRun =
      ((pageCtx bs c.i.toNat).opened && (pageCtx bs c.i.toNat).ppar) :=
    pageCtx_oddRun bs c.i.toNat
  have h14 : (fusedValues c bs73 bs74).or14 = bsW (pageCtx bs c.i.toNat) :=
    fb54_or14_eq_bsW h73' h74'
  have hjb : bitcastVecLanes 8 64
      (unpackLanes 64 4 (bytesToNat bs73) ++
        unpackLanes 64 4 (bytesToNat bs74)) = blockLanes (pageCtx bs c.i.toNat) :=
    fb54_joinBytes_eq_blockLanes _ bs73 bs74 h73' h74'
  have h00 : (fusedValues c bs73 bs74).andII = escAnd00W (pageCtx bs c.i.toNat) := by
    rw [fb54_andII]
    exact hcarry.and00
  have hq : (fusedValues c bs73 bs74).andI = andQuoteW (pageCtx bs c.i.toNat) := by
    rw [fb54_andI_eq_specQuote hjb h14 h00 hst, andQuoteW_spec _ hst]
  refine ⟨?_, ?_, ?_⟩
  · rw [h14, bsW_eq_spec, ← specBackslash64_eq, hklo, hkhi, hkst]
  · rw [ifThen96Mask_eq_specControl h73' h74', hklo, hkhi, hkst]
  · rw [fb54_xorI_eq_specInString hq hcarry.st15 hst, hklo, hkhi, hkst]

/-! ### The carry pair

`carryPair mem a st opened ppar` is the record's sixteen-byte pair and the
classifier state's parity.  Three facts place it: the caller's staged all-false
pair at the first block, the page's own call at the successor, and the successor
classifier carry at the block that call read. -/

/-- **The first block is entered with the staged pair.**  The staging's carry slot
is the all-false pair, and the empty fold's parity is `false`. -/
theorem carryPair_staging {mem : Mem} {b ent xp nxp xcarry xn : Nat}
    {arm : BitVec 64} {bs : List UInt8}
    (hp : S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs) :
    carryPair mem xcarry (classCarryAt (padded bs) ⟨false, false⟩ 0) false false := by
  refine ⟨hp.hxcarry, ?_⟩
  rfl

/-- **A page's call leaves the successor block's pair.**  The escape record's
post stores the pair at the carry slot; its parity is the classifier step's own
at the block's last lane, so the pair is `carryPair` at `carry64`. -/
theorem carryPair_step {mem M : Mem} {blk0 : BitVec 64} {xp xn xcarry xn0 : Nat}
    {position : List Nat} {lo hi : Block32} {st : ClassState}
    (hreach : EscapeReach blk0 xp xn xcarry xn0 position
      (flagBytes (IsBackslashB (hi ⟨31, by decide⟩)) ++
        flagBytes (carry64 lo hi st).oddRun) mem M) :
    carryPair M xcarry (carry64 lo hi st) (IsBackslashB (hi ⟨31, by decide⟩))
      (carry64 lo hi st).oddRun :=
  ⟨hreach.2.2.1, carry64_oddRun_and_self lo hi st⟩

/-- A fold over a list's first `k` bytes is the fold over the list itself at `k`:
taking the prefix twice takes it once. -/
theorem classCarryAt_take_self (bs : List UInt8) (st : ClassState) (k : Nat) :
    classCarryAt (bs.take k) st k = classCarryAt bs st k := by
  unfold classCarryAt
  rw [List.take_take, Nat.min_self]

/-- **The successor block's classifier carry, at the document's own fold.**  The
fold at the next block's offset is the fold over this block's sixty-four bytes,
entered with this block's carry: the document's take splits at the boundary and
the block's sixty-four bytes are `docBlock`. -/
theorem classCarryAt_docBlock_succ (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) :
    classCarryAt (padded bs) ⟨false, false⟩ (64 * (i + 1)) =
      classCarryAt (docBlock bs i)
        (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) 64 := by
  have hlen : ((padded bs).take (64 * i)).length = 64 * i := by
    rw [List.length_take, padded_length]
    omega
  have hstep : classCarryAt (padded bs) ⟨false, false⟩
        (((padded bs).take (64 * i)).length + 64) =
      classCarryAt ((padded bs).drop (64 * i))
        (classCarryAt ((padded bs).take (64 * i)) ⟨false, false⟩
          ((padded bs).take (64 * i)).length) 64 := by
    have h := classCarryAt_append ((padded bs).take (64 * i))
      ((padded bs).drop (64 * i)) ⟨false, false⟩ 64
    rw [show (padded bs).take (64 * i) ++ (padded bs).drop (64 * i) = padded bs from
      List.take_append_drop _ _] at h
    exact h
  rw [show 64 * (i + 1) = ((padded bs).take (64 * i)).length + 64 from by
    rw [hlen]; omega]
  rw [hstep, hlen, classCarryAt_take_self]
  simp only [classCarryAt, docBlock]
  rw [List.take_take, Nat.min_self]

/-- **The successor block's classifier carry, at `carry64`.**  The same identity
in the spelling `carryPair_step` leaves it: `carry64` at the block's halves. -/
theorem classCarryAt_docBlock_succ_carry64 (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) :
    classCarryAt (padded bs) ⟨false, false⟩ (64 * (i + 1)) =
      carry64 (blockLo (padded bs) i) (blockHi (padded bs) i)
        (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) := by
  rw [classCarryAt_docBlock_succ bs hi, carry64_eq_classCarryAt,
    block64_blockLo_blockHi bs hi]

/-! ### The record's `pre` at one call

The staging and the frame give the block's window and the four regions'
separations; what the call supplies beyond them are the count's slot and its domain
bound, the stream's capacity, the block index's cap, the carry pair and the three
mask words. -/

/-- **The record's `pre` at a call site.**  The staging's window is read at the
call's base and block, the separations are the staging's at the count's room, and
the rest is the call's carried state. -/
theorem escapePre_at {budget : List Value → Mem → Nat} {mem0 M : Mem}
    {b ent xp nxp xcarry xn xnA : Nat} {arm : BitVec 64} {bs : List UInt8}
    {next : Nat}
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    (hframe : UnchangedOutside mem0 M
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA))
    (hroom : xnA + 64 ≤ xn + 64 * blocksOf bs.length)
    {i : Nat} (hi : i < blocksOf bs.length)
    (hcount : readBytes M nxp 8 = some (wordBytes 8 xnA))
    (hcount63 : xnA < 2 ^ 63)
    (hcap : HasBytes M xp (4 * blockMax xnA))
    {blk0 : BitVec 64} (hblk0 : blk0.toNat = i)
    {st : ClassState} {prevb prevs : Bool}
    (hpair : carryPair M xcarry st prevb prevs)
    {bsW ctlW imW : BitVec 64}
    (hB : bsW = specBackslash64 (blockLo (padded bs) i) (blockHi (padded bs) i) st)
    (hC : ctlW = specControl64 (blockLo (padded bs) i) (blockHi (padded bs) i) st)
    (hI : imW = specInString64 (blockLo (padded bs) i) (blockHi (padded bs) i) st) :
    (Γ_escape_positions b budget).pre
      [.int 64 bsW, .int 64 ctlW, .int 64 imW, .int 64 blk0, .ptr xp, .ptr nxp,
       .ptr xcarry] M next := by
  have hbmax : blockMax xnA ≤ xn + 64 * blocksOf bs.length + batchReserve := by
    unfold blockMax batchReserve
    omega
  refine ⟨xp, nxp, xcarry, blk0, bsW, ctlW, imW, blockLo (padded bs) i,
    blockHi (padded bs) i, st, prevb, prevs, xnA, rfl, ?_, hB, hC, hI, hpair,
    hcount, hcount63, ?_, ?_, ?_, hcap, ?_⟩
  · have haddr : b + blockAddr blk0 = b + 64 * i := by
      rw [blockAddr, hblk0]
      omega
    rw [haddr, block64_blockLo_blockHi bs hi]
    exact (keep_of_frame hp hframe (by omega)).1 i hi
  · rcases hp.hxpNxp with h | h
    · exact Or.inr (by omega)
    · exact Or.inl h
  · rcases hp.hnxpXc with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rcases hp.hxpXc with h | h
    · exact Or.inr (by omega)
    · exact Or.inl h
  · have hcap' := hp.hblkcap
    rw [hblk0]
    omega

/-- **The record's `pre` at a page's call.**  The three mask words are the page's
own (`page_masks`), and the carried pair the previous call left is the
classifier's carry. -/
theorem page_pre {budget : List Value → Mem → Nat} {mem0 : Mem}
    {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8} {next : Nat}
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    {c : FusedCarry} {bs73 bs74 : List UInt8} {count : Nat} {prevb prevs : Bool}
    (hi : c.i.toNat < blocksOf bs.length)
    (hcarry : PageCarry bs c)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hframe : UnchangedOutside mem0 (fusedStore c bs73 bs74)
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry count))
    (hroom : count + 64 ≤ xn + 64 * blocksOf bs.length)
    (hcount : readBytes (fusedStore c bs73 bs74) nxp 8 = some (wordBytes 8 count))
    (hcount63 : count < 2 ^ 63)
    (hcap : HasBytes (fusedStore c bs73 bs74) xp (4 * blockMax count))
    (hpair : carryPair (fusedStore c bs73 bs74) xcarry
      (classCarryAt (padded bs) ⟨false, false⟩ (64 * c.i.toNat)) prevb prevs) :
    (Γ_escape_positions b budget).pre
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr xp, .ptr nxp, .ptr xcarry] (fusedStore c bs73 bs74) next := by
  obtain ⟨hB, hC, hI⟩ := page_masks bs c bs73 bs74 hi hcarry h73 h74
  exact escapePre_at hp hframe hroom hi hcount hcount63 hcap (blk0 := c.i) rfl
    hpair hB hC hI

/-- **The record's `pre` at the peel's call.**  The peel's entering memory is the
loop's plus the peel's own slot inside the entry array: the frame survives the
store, the count's slot and the carry read through it, and presence survives any
store. -/
theorem peel_pre {budget : List Value → Mem → Nat} {mem0 memL : Mem}
    {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8} {next : Nat}
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    {shr xnA : Nat} {word : List UInt8}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA))
    (hroom : xnA + 64 ≤ xn + 64 * blocksOf bs.length)
    (hcount : readBytes memL nxp 8 = some (wordBytes 8 xnA))
    (hcount63 : xnA < 2 ^ 63)
    (hcap : HasBytes memL xp (4 * blockMax xnA))
    (hwlen : word.length = 8)
    {st : ClassState} {prevb prevs : Bool}
    (hpair : carryPair memL xcarry st prevb prevs)
    {bsW ctlW imW : BitVec 64}
    (hB : bsW = specBackslash64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    (hC : ctlW = specControl64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    (hI : imW = specInString64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st) :
    (Γ_escape_positions b budget).pre
      [.int 64 bsW, .int 64 ctlW, .int 64 imW, .int 64 (BitVec.ofNat 64 shr),
       .ptr xp, .ptr nxp, .ptr xcarry]
      (writeBytes memL (ent + 8 * shr) word) next := by
  have hshr : shr < blocksOf bs.length := by omega
  have hstHi : (ent + 8 * shr) + word.length ≤ ent + 8 * blocksOf bs.length := by
    rw [hwlen]
    omega
  have hframeM : UnchangedOutside mem0 (writeBytes memL (ent + 8 * shr) word)
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA) :=
    frame_write_in_region hframe (Nat.le_add_right _ _) hstHi
  have hcountM : readBytes (writeBytes memL (ent + 8 * shr) word) nxp 8 =
      some (wordBytes 8 xnA) :=
    peel_count_read hp.hentNxp hsucc hwlen hcount
  have hcapM : HasBytes (writeBytes memL (ent + 8 * shr) word) xp
      (4 * blockMax xnA) :=
    hasBytes_writeBytes hcap
  have hpairM : carryPair (writeBytes memL (ent + 8 * shr) word) xcarry st prevb
      prevs := by
    refine ⟨?_, hpair.2⟩
    rw [readBytes_writeBytes_frame memL word (ent + 8 * shr) xcarry 16 ?_]
    · exact hpair.1
    · rcases hp.hentXc with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  have hblk0 : (BitVec.ofNat 64 shr).toNat = shr := by
    rw [BitVec.toNat_ofNat]
    have h1 := hp.hbs63
    have h2 := hp.hblkcap
    omega
  exact escapePre_at hp hframeM hroom hshr hcountM hcount63 hcapM
    (blk0 := BitVec.ofNat 64 shr) hblk0 hpairM hB hC hI

/-! ### The committed compositions at the derived `pre`

`JsonS1BlocksUnitPost.unitPostAt_of_pre`, `peel_unitPostAt_of_pre` and
`JsonS1BlocksFinalAt.tail_calling_at_of_pre` take the record's `pre` as their
first input; these are the same statements at the `pre` derived above. -/

/-- **The unit's post at a page's call, without the record's `pre`.** -/
theorem page_unitPostAt {esc : Calls} {mem0 : Mem}
    {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8} {next : Nat}
    (hEsc : escapeEntryAt esc b)
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    {c : FusedCarry} {bs73 bs74 : List UInt8} {count : Nat} {prevb prevs : Bool}
    (hi : c.i.toNat < blocksOf bs.length)
    (hcarry : PageCarry bs c)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hframe : UnchangedOutside mem0 (fusedStore c bs73 bs74)
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry count))
    (hroom : count + 64 ≤ xn + 64 * blocksOf bs.length)
    (hcount : readBytes (fusedStore c bs73 bs74) nxp 8 = some (wordBytes 8 count))
    (hcount63 : count < 2 ^ 63)
    (hcap : HasBytes (fusedStore c bs73 bs74) xp (4 * blockMax count))
    (hpair : carryPair (fusedStore c bs73 bs74) xcarry
      (classCarryAt (padded bs) ⟨false, false⟩ (64 * c.i.toNat)) prevb prevs) :
    S1BlocksUnitPostAt esc
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr xp, .ptr nxp, .ptr xcarry] (fusedStore c bs73 bs74) next
      c.i xp nxp xcarry count mem0 b ent xn arm bs :=
  unitPostAt_of_pre hEsc
    (page_pre hp hi hcarry h73 h74 hframe hroom hcount hcount63 hcap hpair)
    hcount (by omega) hp hframe hroom

/-- **The unit's post at the peel's call, without the record's `pre`.** -/
theorem peel_unitPostAt {esc : Calls} {mem0 memL : Mem}
    {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8} {next : Nat}
    (hEsc : escapeEntryAt esc b)
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    {shr xnA : Nat} {word : List UInt8}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA))
    (hroom : xnA + 64 ≤ xn + 64 * blocksOf bs.length)
    (hcount : readBytes memL nxp 8 = some (wordBytes 8 xnA))
    (hcount63 : xnA < 2 ^ 63)
    (hcap : HasBytes memL xp (4 * blockMax xnA))
    (hwlen : word.length = 8)
    {st : ClassState} {prevb prevs : Bool}
    (hpair : carryPair memL xcarry st prevb prevs)
    {bsW ctlW imW : BitVec 64}
    (hB : bsW = specBackslash64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    (hC : ctlW = specControl64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    (hI : imW = specInString64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st) :
    S1BlocksUnitPostAt esc
      [.int 64 bsW, .int 64 ctlW, .int 64 imW, .int 64 (BitVec.ofNat 64 shr),
       .ptr xp, .ptr nxp, .ptr xcarry]
      (writeBytes memL (ent + 8 * shr) word) next (BitVec.ofNat 64 shr) xp nxp
      xcarry xnA mem0 b ent xn arm bs :=
  peel_unitPostAt_of_pre hEsc
    (peel_pre hp hsucc hframe hroom hcount hcount63 hcap hwlen hpair hB hC hI)
    (peel_count_read hp.hentNxp hsucc hwlen hcount) (by omega) hp hframe hsucc hwlen
    hroom

/-- **The calling arm's tail at the peel's call, without the record's `pre`.**
`JsonS1BlocksFinalAt.tail_calling_at_of_pre` at the derived `pre`; its statement
is not restated. -/
theorem tail_calling_of_peelPre {esc : Calls} {base : Nat}
    (hEsc : escapeEntryAt esc base)
    {or14 mask xs : BitVec 64} {xp nxp xcarry : Nat} {next : Nat}
    {mem0 memL : Mem} {ent shr xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    {word : List UInt8}
    {start : Mem} {ps : List Nat} {c : FusedCarry} {count pages : Nat}
    (hp : S1BlocksPreAt mem0 base ent xp nxp xcarry xn arm bs)
    {st : ClassState} {prevb prevs : Bool}
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry count))
    (hcount : readBytes memL nxp 8 = some (wordBytes 8 count))
    (hcount63 : count < 2 ^ 63)
    (hcap : HasBytes memL xp (4 * blockMax count))
    (hpair : carryPair memL xcarry st prevb prevs)
    (hroom : count + 64 ≤ xn + 64 * blocksOf bs.length)
    (hsucc : shr + 1 = blocksOf bs.length)
    (hwlen : word.length = 8)
    (hB : or14 = specBackslash64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    (hC : mask = specControl64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    (hI : xs = specInString64 (blockLo (padded bs) shr)
      (blockHi (padded bs) shr) st)
    {or135 andv w : BitVec 64}
    (hstore : writeBytes memL (ent + 8 * shr) word =
      writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8))
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hent : c.ent = ent)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    ∃ M : Mem, S1BlocksTail start ent xp nxp xcarry xn arm bs M :=
  tail_calling_at_of_pre (next := next) (blk0 := BitVec.ofNat 64 shr) hEsc
    (peel_pre (next := next) hp hsucc hframe hroom hcount hcount63 hcap hwlen hpair
      hB hC hI)
    hcount (by omega) hp.hentNxp hp hframe hsucc hwlen hroom hstore hrun hent hshr
    hor hshrEq hand hw harm hxpSep

/-! ### Axiom footprints

`controlWord_eq_specControl` is the mask unit's packed word (`s1_control_eq`) at
the joined byte view; the page's three words are the identity module's and
`PageCarry`'s; the carry pair is `EscapeReach`'s third clause and
`carry64_oddRun_and_self`, and the successor carry is `classCarryAt_append` and
`carry64_eq_classCarryAt`.  `escapePre_at` is the record's `pre`'s existential,
`JsonS1BlocksUnitPost.keep_of_frame` for the window and `omega` for the
separations; the three compositions are the committed lemmas' statements at the
derived `pre`, and none reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.take_append_drop_take
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.block64_blockLo_blockHi
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.controlWord_eq_specControl
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.ifThen96Mask_eq_specControl
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.ifThen150QuoteWord_eq_specControl
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.page_masks
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.carryPair_staging
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.carryPair_step
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.classCarryAt_take_self
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.classCarryAt_docBlock_succ
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.classCarryAt_docBlock_succ_carry64
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.escapePre_at
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.page_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.peel_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.page_unitPostAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.peel_unitPostAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksPagePre.tail_calling_of_peelPre

end LeanLLVM.Refinement.JsonS1BlocksPagePre
