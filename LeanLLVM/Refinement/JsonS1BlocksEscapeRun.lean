/-
The tail's shape at a run whose pages call.

`JsonS1BlocksLoopRun` carries the loop's model-side facts to `for.end101` and
states the tail's first two shapes there, but only in the configuration whose
pages keep silent: `S1BlocksTail`'s third disjunct frames `mem → memL` over the
entry array alone (`EntryFrame mem memL ent (blocksOf bs.length)`), which says
every byte outside the array is the caller's at the loop's exit.  The loop's
escape bit is `%tobool95.not`, i.e. `evalICmp .eq (arm &&& 2) 0`, and a page
takes the escape call exactly when that bit is `0`; on `arm &&& 2 ≠ 0` the bit is
`0` at every page, so every page calls `leanllvm_json_escape_list`, and the call
writes the stream, the count slot and the carry.  The one-region frame is then
false.  What is true is the record's four-region frame, composed across the
pages: the entry array, the stream at the run's count, the count's slot and the
carry.

## The page step

A calling page is the entry store — always inside `(ent, 8 * blocks)` — followed
by the call, whose `EscapeReach` frame is `escapeCallRegions xp nxp xcarry xn'`
at the count the page's own positions produced.  `callFrame_step` carries the
accumulated four-region frame from the page's entering count `xnA` to its leaving
count `xnB`: the frame is widened over the stream
(`escapeCallWriteRegions_widen` — the leaving count's region contains the
entering one, so a byte outside it is outside the narrower region too), the store
leaves the frame in place (`frame_write_in_region`), and the call's three regions
are literally the tail of the four-region list, so `frame_comp` closes the page.

## The page's keeps

The loop's induction reads two facts at a page that calls: the array's prefix at
the successor index and the stream's prefix at its own count.  `callPage_keeps`
reads both out of the record: the array's bytes are outside the call's three
regions (`escapeReach_keepsEntry`), and the prefix below the call's cursor is
outside the *touched* frame, which starts at the cursor — so any shorter prefix
is the caller's too (`streamPrefix_below`, which is
`escapeReach_streamPrefix`'s statement generalized from the cursor to every count
it dominates).

## The chain

`CallChain` is the run's page sequence: each page's store index and word, its
call frame at the count the call left, and the count's monotone step of at most
sixty-four positions — one block's worth, which is the most one block's escape
positions can be.  `CallChain.frame` folds the page step to the whole run, and
`CallChain.count_le` is the count threading: after `n` pages the count is at most
the caller's plus `64 * n`.

## The tail's shape

`S1BlocksCallTail` is `S1BlocksTail`'s third disjunct with the one-region frame
replaced by the composed four-region one, at the count the loop's pages left.
Everything else is the disjunct's own: the loop's prefix at the peel's index and
the peel's slot, the peel's `%or135` at the model, the count the slot holds, the
escape record's `EscapeReach` across the peel's store, and the stream's prefix
below the call's cursor.  `callTail_of_chain` builds it from the carry and the
chain; `callTail_memory` reads the record's four memory clauses — the array, the
count, the stream and the carry pair — and the post's four-region frame at the
run's memory, widening the loop's frame to the count the peel's call reached;
`escapeReach_flag_of_post` reads the unit's post as the shape's reach in the
flag-pair form the disjunct names, and `callTail_of_peel_reach` states the shape
at the memory and word `tail_escape_path`/`tail_escape_run` hand it — the peel's
`writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)`, the index word
`%shr`, and the outcome memory the tail's four steps return.  The shape's last
conjunct is the array's separation at the extent the call *touched*
(`xn0 + position.length`), not at a whole further block's capacity: that is what
`escapeReach_keepsEntry` and the post's frame consume, and the staging's
capacity separation at the caller's count plus the count's room implies it
(`callTail_of_chain`).

## What remains

* The run's own frame, as in the silent lane: `loopRun_carry` exposes no
  per-page frame, so the chain (or, through `callTail_of_chain`'s `hchain.frame`,
  the four-region frame) is the caller's obligation at the loop's exit — the same
  shape in which `JsonS1BlocksLoopRun` takes `EntryFrame`.
* The count the peel's slot holds before the peel's call
  (`readBytes memL nxp 8 = some (wordBytes 8 xn0)`): the loop's per-page call
  outcomes establish it, and the model-side carry does not state it.  It is also
  what identifies the peel's call's own cursor count with the pages' last count,
  which is why `callTail_of_peel_reach` takes both at one number.
* The array's presence at a page's memory, for `callPage_keeps`: the staging's
  `HasBytes` at the caller's memory survives the loop's in-array stores, and the
  record's frame then carries the prefix across the call.
* The page's word identity (`PageModel`), which is `JsonS1BlocksWordIdentities`'s
  lane and not this one: nothing here reads `%or84` or any page value.
-/
import LeanLLVM.Refinement.JsonS1BlocksLoopRun
import LeanLLVM.Refinement.JsonS1BlocksCompose
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonEscapeCallFrame

namespace LeanLLVM.Refinement.JsonS1BlocksEscapeRun

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Which configuration calls

The preheader computes `%tobool95.not` as `evalICmp .eq (arm &&& 2) 0`
(`JsonS1BlocksEntry.lookupName_entryEnv_escape`), and a page takes the escape call
when that bit is `0`.  So the configuration this module frames is exactly
`arm &&& 2 ≠ 0`, which is the condition `S1BlocksTail`'s third disjunct and the
peel's merge arm both carry. -/

/-- **The arm's bit clears the escape bit.**  On `arm &&& 2 ≠ 0` the preheader's
`%tobool95.not` is `0`, so the loop's pages take the escape call. -/
theorem escapeBit_of_arm {arm : BitVec 64} (h : arm &&& 2 ≠ (0 : BitVec 64)) :
    evalICmp .eq (arm &&& 2) 0 = 0 := by
  by_cases hb : (arm &&& 2) = 0
  · exact absurd hb h
  · show BitVec.ofBool (decide ((arm &&& 2) = 0)) = (0 : BitVec 1)
    rw [decide_eq_false hb]
    decide

/-! ### Region widening

`UnchangedOutside` is a per-byte statement about the union of the regions, so a
frame over a narrower stream extent is a frame over a wider one: every byte the
wider region excludes the narrower one excludes too.  This is the move the
page step and the peel's call need, because each call's region starts at the
count the page left and the run's count grows. -/

/-- **The four-region frame widens with the stream's count.**  A frame over the
list at `xnA` is a frame at `xnB ≥ xnA`: the stream region at `xnB` contains the
one at `xnA`, and the other three regions are the same pairs. -/
theorem escapeCallWriteRegions_widen {mem0 m : Mem} {ent blocks xp nxp xcarry xnA xnB : Nat}
    (h : UnchangedOutside mem0 m (escapeCallWriteRegions ent blocks xp nxp xcarry xnA))
    (hxn : xnA ≤ xnB) :
    UnchangedOutside mem0 m (escapeCallWriteRegions ent blocks xp nxp xcarry xnB) :=
  UnchangedOutside.widen h (fun a ha r hr => by
    simp only [escapeCallWriteRegions, escapeCallRegions, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ha (ent, 8 * blocks)
        (by simp [escapeCallWriteRegions, escapeCallRegions])
    · exact fun hc => ha (xp, 4 * (xnB + batchReserve))
        (by simp [escapeCallWriteRegions, escapeCallRegions]) ⟨hc.1, by omega⟩
    · exact ha (nxp, 8) (by simp [escapeCallWriteRegions, escapeCallRegions])
    · exact ha (xcarry, 16)
        (by simp [escapeCallWriteRegions, escapeCallRegions]))

/-- **A store inside a region leaves a frame over that region in place.**  This is
`JsonS1BlocksRecordFrame.frame_write_inside` at a list whose head is the region,
which is how `escapeCallWriteRegions` spells the entry array. -/
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

/-! ### One page

The page's store is inside the entry array; the call's record frame is the three
regions at the count the page's positions produced.  The frame at the page's
entering count is widened to the leaving one, the store leaves it in place, and
the call's three regions are the four-region list's tail. -/

/-- **One calling page carries the frame.**  From the accumulated four-region frame
at `xnA`, a store inside the entry array, and the call's three-region frame at
`xnB ≥ xnA`, the accumulated frame at `xnB` holds. -/
theorem callFrame_step {mem0 mem1 mem2 : Mem} {ent blocks xp nxp xcarry xnA xnB st : Nat}
    {word : List UInt8}
    (hframe : UnchangedOutside mem0 mem1
      (escapeCallWriteRegions ent blocks xp nxp xcarry xnA))
    (hlo : ent ≤ st) (hhi : st + word.length ≤ ent + 8 * blocks)
    (hcall : UnchangedOutside (writeBytes mem1 st word) mem2
      (escapeCallRegions xp nxp xcarry xnB))
    (hle : xnA ≤ xnB) :
    UnchangedOutside mem0 mem2 (escapeCallWriteRegions ent blocks xp nxp xcarry xnB) := by
  have hwide := escapeCallWriteRegions_widen hframe hle
  have hstore := frame_write_in_region hwide hlo hhi
  exact frame_comp hstore hcall (fun r hr => List.mem_cons_of_mem _ hr)

/-! ### The page's keeps, from the record

The loop's induction reads two facts at a page that calls: the array's prefix at
the successor index, and the stream's prefix at the caller's count.  Both are the
record's frame.  The array's bytes are outside the call's three regions by the
staging's separations (`escapeReach_keepsEntry`), and the prefix below this call's
cursor is outside the *touched* frame, which starts at the cursor — so any shorter
prefix is the caller's too, which is what the loop reads at its own count
(`streamPrefix_below`). -/

/-- **The stream's prefix below the cursor is the caller's, at any count the
cursor dominates.**  The touched frame starts at `xp + 4 * xn0`, so every byte of
`[xp, xp + 4 * n)` with `n ≤ xn0` is outside it; the count's slot and the carry
are ordered away from the stream by the staging. -/
theorem streamPrefix_below {blk0 : BitVec 64} {xp nxp xcarry xn0 n : Nat}
    {position : List Nat} {carryBytes : List UInt8} {mem M : Mem}
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position carryBytes mem M)
    (hn : n ≤ xn0)
    (hkeep : nxp + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ nxp)
    (hcx : xcarry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xcarry) :
    readBytes M xp (4 * n) = readBytes mem xp (4 * n) := by
  have hframe : UnchangedOutside mem M
      [(xp + 4 * xn0, 4 * (position.length + batchReserve)), (nxp, 8), (xcarry, 16)] := by
    simpa only [touchedRegions] using escapeReach_callTouched hreach
  refine readBytes_of_outside_three hframe ?_ ?_ ?_
  · intro k hk
    rintro ⟨h1, h2⟩
    omega
  · intro k hk
    rintro ⟨h1, h2⟩
    unfold blockMax batchReserve at *
    rcases hkeep with hh | hh <;> omega
  · intro k hk
    rintro ⟨h1, h2⟩
    unfold blockMax batchReserve at *
    rcases hcx with hh | hh <;> omega

/-- **A calling page's keeps.**  The array's prefix at any extent the block count
dominates, and the stream's prefix at the caller's count (`xn ≤ xn0`), both read
back after the call.  These are the two facts the loop's induction reads at
`hkeep`; the record's frame is what supplies them. -/
theorem callPage_keeps {blk0 : BitVec 64} {xp nxp xcarry xn0 xn : Nat}
    {position ps : List Nat} {opened ppar : Bool} {mem M : Mem} {ent : Nat}
    {bs : List UInt8} {k : Nat}
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar) mem M)
    (hpresent : ∃ l, readBytes mem ent (8 * blocksOf bs.length) = some l)
    (hk : k ≤ blocksOf bs.length)
    (hprefix : EntryPrefix mem ent bs k)
    (hn : xn ≤ xn0)
    (hstream : readBytes mem xp (4 * xn) = some (positionsBytes 4 ps))
    (hentXp : ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ ent)
    (hentNxp : ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent)
    (hentXc : ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ ent)
    (hkeep : nxp + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ nxp)
    (hcx : xcarry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xcarry) :
    EntryPrefix M ent bs k ∧ StreamPrefix M xp xn ps := by
  obtain ⟨l, hl⟩ := hpresent
  have hlM : readBytes M ent (8 * blocksOf bs.length) = some l := by
    rw [escapeReach_keepsEntry hreach hentXp hentNxp hentXc]
    exact hl
  refine ⟨entryPrefix_of_eq hl hlM hk hprefix, ?_⟩
  unfold StreamPrefix
  rw [streamPrefix_below hreach hn hkeep hcx]
  exact hstream

/-! ### The run's calling pages

One chain node per page.  The node records the page's store index and word (both
inside the entry array), the call's three-region frame at the count the call
left, and the count's step: monotone and at most sixty-four positions. -/

/-- **The loop's calling pages.**  A chain from the caller's memory and count to
the memory and count the pages left.  `n` is the number of pages. -/
inductive CallChain (ent blocks xp nxp xcarry xn : Nat) (start : Mem) :
    Mem → Nat → Nat → Prop where
  /-- The caller's memory, at the caller's count, with no page run. -/
  | nil : CallChain ent blocks xp nxp xcarry xn start start xn 0
  /-- One page: the store inside the entry array, the call's three regions at the
  count the call left, and the count's step. -/
  | step {mem0 mem2 : Mem} {xnA xnB n st : Nat} {word : List UInt8} :
      CallChain ent blocks xp nxp xcarry xn start mem0 xnA n →
      ent ≤ st →
      st + word.length ≤ ent + 8 * blocks →
      UnchangedOutside (writeBytes mem0 st word) mem2
        (escapeCallRegions xp nxp xcarry xnB) →
      xnA ≤ xnB →
      xnB ≤ xnA + 64 →
      CallChain ent blocks xp nxp xcarry xn start mem2 xnB (n + 1)

/-- **The chain's frame.**  The page step folds: at the end of the pages the
four-region frame holds from the caller's memory to the pages' memory, at the
count the last page's call left. -/
theorem CallChain.frame {ent blocks xp nxp xcarry xn : Nat} {start : Mem} :
    ∀ {mem : Mem} {count n : Nat},
      CallChain ent blocks xp nxp xcarry xn start mem count n →
      UnchangedOutside start mem
        (escapeCallWriteRegions ent blocks xp nxp xcarry count) := by
  intro mem count n h
  induction h with
  | nil => exact fun a _ => rfl
  | step hc hlo hhi hcall hle hlen ih =>
      exact callFrame_step ih hlo hhi hcall hle

/-- **The count's threading.**  Each page adds at most one block's worth of
positions, so after `n` pages the count is at most the caller's plus `64 * n`. -/
theorem CallChain.count_le {ent blocks xp nxp xcarry xn : Nat} {start : Mem} :
    ∀ {mem : Mem} {count n : Nat},
      CallChain ent blocks xp nxp xcarry xn start mem count n →
      count ≤ xn + 64 * n := by
  intro mem count n h
  induction h with
  | nil => omega
  | step hc hlo hhi hcall hle hlen ih => omega

/-- **A chain step from the record's per-call reach.**  The call's frame widened to
the block's three regions (`escapeReach_callRegions`) is the chain step's, and the
count advances by exactly the positions the call wrote — at most a block's worth. -/
theorem CallChain.step_of_reach {ent blocks xp nxp xcarry xn : Nat} {start : Mem}
    {mem0 mem2 : Mem} {count n st : Nat} {word : List UInt8}
    {blk0 : BitVec 64} {position : List Nat} {opened ppar : Bool}
    (hc : CallChain ent blocks xp nxp xcarry xn start mem0 count n)
    (hlo : ent ≤ st) (hhi : st + word.length ≤ ent + 8 * blocks)
    (hreach : EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar) (writeBytes mem0 st word) mem2)
    (hlen : position.length ≤ 64) :
    CallChain ent blocks xp nxp xcarry xn start mem2 (count + position.length) (n + 1) :=
  CallChain.step hc hlo hhi (escapeReach_callRegions hreach) (by omega) (by omega)

/-! ### The tail's shape at a calling run

The committed `S1BlocksTail`'s third disjunct, with the single-region frame
replaced by the composed four-region one.  The count `xn0` is the one the pages
left — the count the peel's call is entered with — and the room below it is the
last block's own. -/

/-- **The tail's shape when the pages call.**  `memL` is the loop's exit memory;
the frame from the caller's memory is the four regions at the pages' count, the
array and the peel's slot are the loop's and the peel's, the count and the
stream's prefix are read at `xn0`, and the peel's call is the record's
`EscapeReach` across the peel's store. -/
def S1BlocksCallTail (mem : Mem) (ent xp nxp xcarry xn : Nat) (arm : BitVec 64)
    (bs : List UInt8) (M : Mem) : Prop :=
  ∃ (memL : Mem) (shr xn0 : Nat) (or135 andv w blk0 : BitVec 64)
      (position ps0 : List Nat) (opened ppar : Bool),
    UnchangedOutside mem memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xn0) ∧
    EntryPrefix memL ent bs shr ∧
    shr + 1 = blocksOf bs.length ∧
    PeelWordAtModel or135 bs shr ∧
    shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat ∧
    andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64 ∧
    w = or135 &&& limMask andv.toNat ∧
    arm &&& 2 ≠ (0 : BitVec 64) ∧
    readBytes memL nxp 8 = some (wordBytes 8 xn0) ∧
    EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) M ∧
    StreamPrefix memL xp xn0 ps0 ∧
    position.length ≤ 64 ∧
    xn0 + 64 ≤ xn + 64 * blocksOf bs.length ∧
    (ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ ent)

/-- **The shape, from the carry and the pages.**  The chain supplies the frame and
the count's threading; `pages + 1 ≤ blocks` is the peel's own page counted with
the loop's, so the count's room is the last block's. -/
theorem callTail_of_chain {mem0 : Mem} {xp xn nxp xcarry : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {arm : BitVec 64}
    {shr xn0 pages : Nat} {or135 andv w blk0 : BitVec 64}
    {position ps0 : List Nat} {opened ppar : Bool} {M : Mem}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hchain : CallChain c.ent (blocksOf bs.length) xp nxp xcarry xn mem0 c.mem xn0 pages)
    (hpages : pages + 1 ≤ blocksOf bs.length)
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hcountL : readBytes c.mem nxp 8 = some (wordBytes 8 xn0))
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) M)
    (hstream : StreamPrefix c.mem xp xn0 ps0)
    (hlen : position.length ≤ 64)
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    S1BlocksCallTail mem0 c.ent xp nxp xcarry xn arm bs M := by
  subst shr
  have hcountLe := hchain.count_le
  have hroom : xn0 + 64 ≤ xn + 64 * blocksOf bs.length := by omega
  have hxpSep' : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ c.ent := by
    rcases hxpSep with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by omega)
  exact ⟨c.mem, c.i.toNat, xn0, or135, andv, w, blk0, position, ps0, opened, ppar,
    hchain.frame, hc.arrPrefix, hsucc, hor, hshrEq, hand, hw, harm, hcountL, hreach,
    hstream, hlen, hroom, hxpSep'⟩

/-! ### The record's clauses at the run's memory

The shape's parts are the post's memory conjuncts: the array (the loop's prefix,
the peel's slot, kept across the call), the count, the stream at the caller's
prefix plus the peel's segment, the carry pair, and the post's four-region frame
widened from the pages' count to the count the peel's call reached.  The staging's
separations of the array from the call's three regions and of the stream from the
count and the carry are the caller's, exactly as in `escape_arm_memory`. -/

/-- **The record's memory clauses at the calling run's memory.**  The entry array
is the model's whole array, the count is the pages' plus the peel's positions, the
stream is the caller's prefix plus the peel's segment, the carry is a flag pair,
and the frame is the post's four regions at the call's own count. -/
theorem callTail_memory {mem M : Mem} {ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hbs63 : bs.length < 2 ^ 63)
    (h : S1BlocksCallTail mem ent xp nxp xcarry xn arm bs M)
    (hxnSep : ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent)
    (hxcSep : ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ ent)
    (hxpNxp : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
      nxp + 8 ≤ xp)
    (hxpXc : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
      xcarry + 16 ≤ xp) :
    ∃ (xn0 shr : Nat) (blk0 : BitVec 64) (position ps0 : List Nat),
      readBytes M ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) ∧
      readBytes M nxp 8 = some (wordBytes 8 (xn0 + position.length)) ∧
      readBytes M xp (4 * (xn0 + position.length)) =
        some (positionsBytes 4 (ps0 ++ position.map fun k => blockAddr blk0 + k)) ∧
      (∃ (st : ClassState) (prevb prevs : Bool), carryPair M xcarry st prevb prevs) ∧
      UnchangedOutside mem M
        (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry
          (xn0 + position.length)) := by
  obtain ⟨memL, shr, xn0, or135, andv, w, blk0, position, ps0, opened, ppar,
    hloopFrame, hprefix, hsucc, hor, hshrEq, hand, hw, harm, hcountL, hreach,
    hstream, hlen, hroom, hxpSep⟩ := h
  -- the peel's word is the model's: `%and` is the remainder and `%shr` the whole
  -- blocks, so the clamp is the model's at the peel's slot
  have hnlt : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have handv : andv.toNat = bs.length % 64 := by
    rw [hand, and_sixtythree_toNat, hnlt]
  have hshrv : shr = bs.length / 64 := by
    rw [hshrEq, ushr_six_toNat, hnlt]
  have hlim := limMask_index_eq handv hshrv
  have hslot := peel_slot_read (mem := memL) (ent := ent) (shr := shr) hor hlim
  rw [← hw] at hslot
  -- the array at the peel's memory, and the call's silence outside its regions
  have hentL : readBytes (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8))
      ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) :=
    entryWords_of_prefix_store hsucc (entryPrefix_read (by omega) hprefix) hslot
  have hentM := escapeReach_keepsEntry hreach hxpSep hxnSep hxcSep
  -- the stream's prefix below the cursor, through the peel's store and the call
  have hpeelFrame : EntryFrame memL
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) ent
      (blocksOf bs.length) :=
    peelStore_frame (mem0 := memL) (fun a _ => rfl) hsucc
      (natToBytes_length w.toNat 8)
  have hsepPeel : ent + 8 * blocksOf bs.length ≤ xp ∨ xp + 4 * xn0 ≤ ent := by omega
  have hprefixPeel : readBytes
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) xp (4 * xn0) =
        some (positionsBytes 4 ps0) := by
    rw [readBytes_frame_single hpeelFrame hsepPeel]
    exact hstream
  have hkeep : nxp + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ nxp := by
    unfold blockMax batchReserve at *
    rcases hxpNxp with hh | hh
    · exact Or.inr (by omega)
    · exact Or.inl hh
  have hcx : xcarry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xcarry := by
    unfold blockMax batchReserve at *
    rcases hxpXc with hh | hh
    · exact Or.inr (by omega)
    · exact Or.inl hh
  have hstreamM : StreamPrefix M xp xn0 ps0 :=
    escapeReach_streamPrefix hreach hkeep hcx hprefixPeel
  obtain ⟨hcount, hstreamOut, hpair⟩ := escapeClauses_of_reach hreach hstreamM
  -- the frame: the pages' at the peel's count, widened past the call's segment
  have hwide : UnchangedOutside mem memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry
        (xn0 + position.length)) :=
    escapeCallWriteRegions_widen (ent := ent) (blocks := blocksOf bs.length)
      (xp := xp) (nxp := nxp) (xcarry := xcarry) (xnA := xn0)
      (xnB := xn0 + position.length) hloopFrame (by omega)
  have hlo : ent ≤ ent + 8 * shr := by omega
  have hhi : ent + 8 * shr + (natToBytes w.toNat 8).length ≤
      ent + 8 * blocksOf bs.length := by
    rw [natToBytes_length]
    omega
  have hstoreFrame := frame_write_in_region hwide hlo hhi
  refine ⟨xn0, shr, blk0, position, ps0, ?_, hcount, hstreamOut, hpair, ?_⟩
  · rw [hentM]
    exact hentL
  · exact frame_comp hstoreFrame (escapeReach_callRegions hreach)
      (fun r hr => List.mem_cons_of_mem _ hr)

/-! ### The record's post, as the shape's reach

`EscapeReach` carries the call's carry list as an argument.  The unit's post fixes
it: its carry clause is `carryPair` at the block's own flags, so the list is a
flag pair, which is the form `S1BlocksCallTail` names. -/

/-- **The unit's post, as the shape's reach.**  The post fixes the carry list as
the pair of its own two flags, so the record's reach is stated in the flag form the
tail's disjunct uses.  This is `escapeReach_of_post` with the carry's witnesses
named. -/
theorem escapeReach_flag_of_post {base : Nat} {bs ctl im blk0 : BitVec 64}
    {xp xn carry : Nat} {mem M : Mem}
    (h : escapePositionsPost base
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn, .ptr carry]
      mem M) :
    ∃ (xn0 : Nat) (position : List Nat) (opened ppar : Bool),
      EscapeReach blk0 xp xn carry xn0 position
        (flagBytes opened ++ flagBytes ppar) mem M := by
  obtain ⟨xp', xn', carry', blk0', bs', ctl', im', lo, hi, st, prevb, prevs, xn0,
    hargs, _hblock, _hbs, _hctl, _him, _hpairIn, _hcntIn, _hxn0, hcntOut, hposOut,
    hpairOut, hhasOut, hframeOut⟩ := h
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨_hbsE, _hctlE, _himE, hblkE, hxpE, hxnE, hcarryE⟩ := hargs
  subst hxpE; subst hxnE; subst hcarryE
  have hblkEq : blk0' = blk0 := (eq_of_heq hblkE).symm
  subst hblkEq
  refine ⟨xn0, escapePositionsFrom (block64 lo hi) st,
    IsBackslashB (hi ⟨31, by decide⟩), (carry64 lo hi st).oddRun, ?_, ?_,
    hpairOut.1, hhasOut, ?_⟩
  · simpa using hcntOut
  · simpa [blockPositions] using hposOut
  · simpa using hframeOut

/-! ### The peel's own step

`tail_escape_path` gives the reach at the memory `if.then103`'s store leaves —
`writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)` — and `tail_escape_run`
returns that call's memory after the tail's four steps.  This is the shape at
exactly those numbers: the loop's memory is the state's, the store's address is
the peel's slot, and the peel's index word is the state's `%shr`. -/

/-- **The shape at the peel's own memory and word.**  The reach is
`tail_escape_path`'s: same pre-memory, same index word `%shr`, same outcome
memory.  `shrV.toNat = c.i.toNat` identifies the peel's index word with the
carry's slot index, and `v.arrayidx = c.ent + 8 * c.i.toNat` with `v.and137 = w`
the store. -/
theorem callTail_of_peel_reach {mem0 : Mem} {s : State} {v : IfThen103Values}
    {xp xn nxp xcarry : Nat} {ps : List Nat} {bs : List UInt8} {c : FusedCarry}
    {arm : BitVec 64} {shrV : BitVec 64} {xn0 pages shr : Nat}
    {or135 andv w : BitVec 64} {position ps0 : List Nat}
    {opened ppar : Bool} {M : Mem}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hchain : CallChain c.ent (blocksOf bs.length) xp nxp xcarry xn mem0 c.mem xn0 pages)
    (hpages : pages + 1 ≤ blocksOf bs.length)
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hshr : shr = c.i.toNat)
    (hshrV : shrV.toNat = c.i.toNat)
    (hsM : s.mem = c.mem)
    (harrm : v.arrayidx = c.ent + 8 * c.i.toNat)
    (hword : v.and137 = w)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hcountL : readBytes c.mem nxp 8 = some (wordBytes 8 xn0))
    (hreach : EscapeReach shrV xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) M)
    (hstream : StreamPrefix c.mem xp xn0 ps0)
    (hlen : position.length ≤ 64)
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    S1BlocksCallTail mem0 c.ent xp nxp xcarry xn arm bs M := by
  subst shr
  rw [hsM, harrm, hword] at hreach
  exact callTail_of_chain hc hchain hpages hsucc rfl hor hshrEq hand hw harm
    hcountL hreach hstream hlen hxpSep

/-! ### Axiom footprints

The region algebra, the prefix reads and the arm's bit are `UnchangedOutside`'s
per-byte definition, the record's frame and `evalICmp`: `escapeBit_of_arm`,
`escapeCallWriteRegions_widen`, `streamPrefix_below`, `callPage_keeps`,
`CallChain.count_le`, `CallChain.step_of_reach`, `S1BlocksCallTail` and
`escapeReach_flag_of_post` read only `propext` and `Quot.sound`; `CallChain` is an
inductive and depends on nothing.  `Classical.choice` is the carrier of the store
algebra and the peel's slot projection — `frame_write_in_region` (through
`readByte_writeBytes_outside`), `callFrame_step`, `CallChain.frame`,
`callTail_of_chain`, `callTail_memory` (through `JsonS1BlocksSatisfies.peel_slot_read`)
and `callTail_of_peel_reach` — the same carrier `JsonS1BlocksRecordFrame` reports
for its store and frame statements.  No statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.escapeBit_of_arm
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.escapeCallWriteRegions_widen
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.frame_write_in_region
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.callFrame_step
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.streamPrefix_below
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.callPage_keeps
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.CallChain
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.CallChain.frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.CallChain.count_le
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.CallChain.step_of_reach
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.S1BlocksCallTail
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.callTail_of_chain
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.callTail_memory
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.escapeReach_flag_of_post
#print axioms LeanLLVM.Refinement.JsonS1BlocksEscapeRun.callTail_of_peel_reach

end LeanLLVM.Refinement.JsonS1BlocksEscapeRun
