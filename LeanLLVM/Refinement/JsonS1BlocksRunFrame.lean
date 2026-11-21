/-
The loop's calling run: the per-page frame chain, the count's slot, and the
array's presence at the loop's exit.

`JsonS1BlocksLoopRun.loopRun_carry` carries the model-side facts to
`for.end101`, and `JsonS1BlocksEscapeRun.callTail_of_chain` builds the tail's
third disjunct from a `CallChain`, the count the peel's slot holds and the
stream's prefix — but no theorem in the tree produces those three facts from the
run.  The one-region `EntryFrame` the loop's exit theorems take is the *silent*
configuration's; on `arm &&& 2 ≠ 0` every page calls `leanllvm_json_escape_list`,
so the caller's frame is the record's four regions and the run's memory is the
caller's only outside the entry array, the stream, the count's slot and the
carry.

## The carried facts

* **`FrameCarry`** — the chain's carry at one loop head: the `CallChain` from the
  run's starting memory to the page's memory at the count the pages left, the
  count's slot at that count, the stream's prefix at that count, and the entry
  array's presence.  It is the per-page frame the `LoopCarry` does not state.
* **`RunFrame`** — the exit bundle: the model-side `LoopCarry`, the `FrameCarry`,
  the peel's index as the last block, and the pages' extent below the document's
  block count.

## What is proved

* `callPage_present` — **the array's presence at a page's memory**: a staged
  range outside the escape call's three regions is still present after the call.
  This is the premise `callPage_keeps` reads (`hpresent`), and it is what lets the
  induction keep the array present across every page.
* `frameCarry_step` — **one page advances the chain**: the page's store is inside
  the entry array (`fusedValues_arrayidx`, `natToBytes_length`), the call's record
  frame is the three regions at the count the page left, and the count's slot,
  the stream's prefix and the array's presence are the reach's own clauses.  The
  step is `CallChain.step_of_reach`.
* `loopPage_zero` — **one calling page**: with the loop's escape bit `0` the page
  reaches the latch on the DFA arm's or the merge arm's escape record, and the
  page's keeps — the array's prefix at the successor index and the stream's
  prefix at the caller's count — are `callPage_keeps`'s, read from the record and
  the staged presence rather than taken as premises.
* `loopRun_frame` — **the induction**: one page per row carries `LoopInv` and
  `FrameCarry` to `for.end101`, and at the exit states `RunFrame`: the chain
  `mem0 → c.mem` at the pages' count, the count's slot, the stream's prefix, the
  array's presence, and the peel's index.
* `runFrame_writeRegions` — **the run's own frame** at the exit: `CallChain.frame`
  at the bundle's end, the four-region `UnchangedOutside` the post's calling
  shape needs.
* `count_slot_read`, `stream_prefix_at_exit`, `array_present_at_exit` — the
  bundle's three facts read back: the count `callTail_of_chain` names `hcountL`,
  the stream it names `hstream`, and the presence `callPage_keeps` reads.
* `tail_third_of_frame` — **the tail's third disjunct** from a `RunFrame` and the
  peel's reach, by `callTail_of_chain`.  The disjunct is `S1BlocksTail`'s
  `Or.inr (Or.inr ·)`, not a private shape.

## What remains

* **The page's word identity** (`PageModel`): the loop's store word is the
  model's entry word.  The chain advances the carry, so it reads it, and the
  induction takes it as `hstoreAll` — the store clause at the page's loaded
  words — rather than through `PageModel`'s field, so that the classifier lane
  can keep sharpening that structure without forcing this lane to restate it.
* **The escape unit's per-page record** (`hreach`): the call's `EscapeReach` at
  the page's count.  It is the unit's post, not the loop's, and the loop lane
  never states it; the chain's step and the page's keeps both read it.
* **The document and the staged zeroes at the call's memory** (`hkeep`): the
  record's frame does not restate the document window; the page that calls
  writes only the three regions, and the caller's staging orders them away from
  the window.
* **The exit's fuel**: `loopRun_frame` bounds the run by
  `5 * (%shr - (%i + 1)) + 5`, the same charge `loopRun_carry` exposes; its
  containment in the record's budget is `s1BlocksBudget_of_phaseCharge`'s and is
  not restated here.
-/
import LeanLLVM.Refinement.JsonS1BlocksEscapeRun
import LeanLLVM.Refinement.JsonS1BlocksLoopRun
import LeanLLVM.Refinement.JsonS1BlocksRecordFrame
import LeanLLVM.Refinement.JsonS1BlocksSeparation

namespace LeanLLVM.Refinement.JsonS1BlocksRunFrame

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksSeparation

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The chain's carry at one loop head

The facts the pages' calls preserve and the loop's model-side carry does not
state.  The chain runs from the memory the run started at to the page's own
memory, ending at the count the pages have written; the count's slot holds that
count, the stream's prefix is the pages' concatenation, and the entry array is
still there. -/

/-- **The calling run's carry at one loop head.** -/
structure FrameCarry (start : Mem) (xp xn nxp xcarry : Nat) (bs : List UInt8)
    (c : FusedCarry) (count pages : Nat) : Prop where
  /-- The page sequence: the run's calls, from the starting memory to this one. -/
  chain : CallChain c.ent (blocksOf bs.length) xp nxp xcarry xn start c.mem count pages
  /-- The count's slot holds the count the pages left. -/
  countRead : readBytes c.mem nxp 8 = some (wordBytes 8 count)
  /-- The stream's prefix at that count. -/
  stream : ∃ ps : List Nat, readBytes c.mem xp (4 * count) = some (positionsBytes 4 ps)
  /-- The entry array is present at the page's memory. -/
  present : HasBytes c.mem c.ent (8 * blocksOf bs.length)

/-- **The exit's three facts.**  The model-side carry, the chain's carry, the
peel's index as the document's last block, and the pages' extent: one page per
block, plus the peel's own. -/
structure RunFrame (start : Mem) (xp xn nxp xcarry : Nat) (ps : List Nat)
    (bs : List UInt8) (c : FusedCarry) (count pages : Nat) : Prop where
  /-- The loop's model-side facts. -/
  carry : LoopCarry start xp xn ps bs c
  /-- The chain's facts at the run's memory. -/
  frame : FrameCarry start xp xn nxp xcarry bs c count pages
  /-- The peel's index is the last block. -/
  succ : c.i.toNat + 1 = blocksOf bs.length
  /-- The loop's pages and the peel's are the document's blocks. -/
  pagesLe : pages + 1 ≤ blocksOf bs.length

/-- The chain's count never falls below the caller's. -/
theorem CallChain.count_ge {ent blocks xp nxp xcarry xn : Nat} {start : Mem} :
    ∀ {mem : Mem} {count n : Nat},
      CallChain ent blocks xp nxp xcarry xn start mem count n → xn ≤ count := by
  intro mem count n h
  induction h with
  | nil => omega
  | step hc hlo hhi hcall hle hlen ih => omega

/-! ### The array's presence at a page's memory

`callPage_keeps` reads the array back after the call, but it needs the array to
be present at the call's entering memory (`hpresent`).  The presence is the
staging's and survives the loop's stores (`hasBytes_writeBytes`); the call then
leaves the range alone, because the array is separated from its three regions. -/

/-- **The array's presence at a page's memory.**  A staged array the escape call
cannot reach is still present at the call's outcome: the range's bytes are
outside the three regions the record's frame names. -/
theorem callPage_present {blk0 : BitVec 64} {xp nxp xcarry xn0 : Nat}
    {position : List Nat} {opened ppar : Bool} {mem M : Mem} {ent blocks : Nat}
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar) mem M)
    (hpresent : HasBytes mem ent (8 * blocks))
    (hentXp : ent + 8 * blocks ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ ent)
    (hentXn : ent + 8 * blocks ≤ nxp ∨ nxp + 8 ≤ ent)
    (hentCarry : ent + 8 * blocks ≤ xcarry ∨ xcarry + 16 ≤ ent) :
    HasBytes M ent (8 * blocks) := by
  refine hasBytes_of_outside_three (escapeReach_callRegions hreach) ?_ ?_ ?_ hpresent
  · intro k _
    exact outside_of_separated hentXp (by omega) (by omega)
  · intro k _
    exact outside_of_separated hentXn (by omega) (by omega)
  · intro k _
    exact outside_of_separated hentCarry (by omega) (by omega)

/-! ### The page's frame step

The page's store, at `%ent + 8 * %i`, is the entry array's slot, and the call's
record is the other three regions.  The `EscapeReach` is stated at the store's own
memory, so the chain step is `CallChain.step_of_reach`; the count's slot, the
stream's segment and the array's presence are the reach's clauses at the page's
own numbers. -/

/-- **One calling page advances the chain.**  From the old carry, the page's
store and the call's reach at the page's count, the successor's carry holds: the
chain gains one node, the count is the call's own, the stream is the prefix plus
the call's segment, and the array is still present. -/
theorem frameCarry_step {start : Mem} {xp xn nxp xcarry : Nat} {bs : List UInt8}
    {c : FusedCarry} {count pages : Nat} {bs73 bs74 : List UInt8}
    {u8k : List (BitVec 64)} {M : Mem}
    (hframe : FrameCarry start xp xn nxp xcarry bs c count pages)
    (hi : c.i.toNat < blocksOf bs.length)
    (hsep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hsepN : c.ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ c.ent)
    (hsepC : c.ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ c.ent)
    (hcountRoom : count + 64 ≤ xn + 64 * blocksOf bs.length)
    (hkeepXp : nxp + 8 ≤ xp ∨ xp + 4 * blockMax count ≤ nxp)
    (hkeepXc : xcarry + 16 ≤ xp ∨ xp + 4 * blockMax count ≤ xcarry)
    {blk0 : BitVec 64} {position : List Nat} {opened ppar : Bool}
    (hreach : EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar) (fusedStore c bs73 bs74) M)
    (hlen : position.length ≤ 64) :
    FrameCarry start xp xn nxp xcarry bs (fusedNext c bs73 bs74 u8k M)
      (count + position.length) (pages + 1) := by
  have hcountR := hreach.1
  have hseg := hreach.2.1
  have hst : (fusedValues c bs73 bs74).arrayidx = c.ent + 8 * c.i.toNat :=
    fusedValues_arrayidx c bs73 bs74
  have hlo : c.ent ≤ (fusedValues c bs73 bs74).arrayidx := by rw [hst]; omega
  have hhi : (fusedValues c bs73 bs74).arrayidx +
      (natToBytes (fusedValues c bs73 bs74).or84.toNat 8).length ≤
      c.ent + 8 * blocksOf bs.length := by
    rw [hst, natToBytes_length]; omega
  obtain ⟨ps0, hps0⟩ := hframe.stream
  have hstoreStream : readBytes (fusedStore c bs73 bs74) xp (4 * count) =
      some (positionsBytes 4 ps0) := by
    show readBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
      (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) xp (4 * count) =
        some (positionsBytes 4 ps0)
    rw [fusedValues_arrayidx, readBytes_writeBytes_frame c.mem _
      (c.ent + 8 * c.i.toNat) xp (4 * count) ?_]
    · exact hps0
    · rcases hsep with h | h
      · refine Or.inr ?_
        have h8 : 8 * (c.i.toNat + 1) ≤ 8 * blocksOf bs.length :=
          Nat.mul_le_mul_left 8 (by omega)
        have h8' : 8 * c.i.toNat + 8 ≤ 8 * blocksOf bs.length := by
          simpa [Nat.mul_add, Nat.mul_one] using h8
        calc (c.ent + 8 * c.i.toNat) + 8 = c.ent + (8 * c.i.toNat + 8) := by omega
          _ ≤ c.ent + 8 * blocksOf bs.length := Nat.add_le_add_left h8' c.ent
          _ ≤ xp := h
      · refine Or.inl ?_
        have h4 : 4 * count ≤
            4 * (xn + 64 * blocksOf bs.length + batchReserve) :=
          Nat.mul_le_mul_left 4 (by omega)
        calc xp + 4 * count ≤ xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) :=
              Nat.add_le_add_left h4 xp
          _ ≤ c.ent := h
          _ ≤ c.ent + 8 * c.i.toNat := Nat.le_add_right _ _
  have hpresentPre : HasBytes (fusedStore c bs73 bs74) c.ent
      (8 * blocksOf bs.length) := by
    show HasBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
      (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) c.ent
        (8 * blocksOf bs.length)
    exact hasBytes_writeBytes hframe.present
  refine
    { chain := ?_
      countRead := ?_
      stream := ?_
      present := ?_ }
  · show CallChain (fusedNext c bs73 bs74 u8k M).ent (blocksOf bs.length) xp nxp
      xcarry xn start (fusedNext c bs73 bs74 u8k M).mem
        (count + position.length) (pages + 1)
    exact CallChain.step_of_reach hframe.chain hlo hhi
      (by
        show EscapeReach blk0 xp nxp xcarry count position
          (flagBytes opened ++ flagBytes ppar)
          (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
            (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) M
        exact hreach)
      hlen
  · show readBytes M nxp 8 = some (wordBytes 8 (count + position.length))
    exact hcountR
  · have hstreamM : readBytes M xp (4 * count) = some (positionsBytes 4 ps0) :=
      escapeReach_streamPrefix hreach hkeepXp hkeepXc hstoreStream
    refine ⟨ps0 ++ position.map (fun k => blockAddr blk0 + k), ?_⟩
    show readBytes M xp (4 * (count + position.length)) =
      some (positionsBytes 4 (ps0 ++ position.map (fun k => blockAddr blk0 + k)))
    rw [show 4 * (count + position.length) = 4 * count + 4 * position.length
        from by omega,
      readBytes_append M (4 * count) xp (positionsBytes 4 ps0)
        (4 * position.length)
        (positionsBytes 4 (position.map (fun k => blockAddr blk0 + k)))
        hstreamM hseg,
      positionsBytes_append]
  · show HasBytes M c.ent (8 * blocksOf bs.length)
    refine callPage_present hreach hpresentPre ?_ hsepN hsepC
    rcases hsep with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have h4 : 4 * (count + position.length + batchReserve) ≤
          4 * (xn + 64 * blocksOf bs.length + batchReserve) :=
        Nat.mul_le_mul_left 4 (by omega)
      calc xp + 4 * (count + position.length + batchReserve)
          ≤ xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) :=
            Nat.add_le_add_left h4 xp
        _ ≤ c.ent := h

/-! ### The page, on the calling configuration

The loop's escape bit `%tobool95.not` is `0` on `arm &&& 2 ≠ 0`
(`JsonS1BlocksEscapeRun.escapeBit_of_arm`), so every page takes the call.  The
page's two shapes are the DFA arm's escape record and the merge arm's; the skip
arms are the other configuration's.  The page's keeps come from
`callPage_keeps`: the entry array's prefix at the successor index from the page's
store identity, and the stream's prefix at the caller's count from the staged
stream, both read back through the call's record. -/

/-- **One page on the escape configuration.**  From the head's invariant, the
model's carry and the chain's carry, the page reaches the latch at the
successor's carry and at the same memory the call returned, in at most four
control steps; the chain, the count's slot, the stream's prefix and the array's
presence advance with it. -/
theorem loopPage_zero (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (start : Mem) (xp xn nxp xcarry : Nat) (bs : List UInt8)
    (ps : List Nat) (count pages : Nat) (r : CallOutcome)
    (hinv : FusedInv env s c gate 0)
    (hcarry : LoopCarry start xp xn ps bs c)
    (hframe : FrameCarry start xp xn nxp xcarry bs c count pages)
    (hstore : (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hentNxp : c.ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ c.ent)
    (hentXc : c.ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ c.ent)
    (hxpNxp : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
      nxp + 8 ≤ xp)
    (hxpXc : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
      xcarry + 16 ≤ xp)
    (hcountRoom : count + 64 ≤ xn + 64 * blocksOf bs.length)
    (hkeepDoc : ∀ j, j < c.shr.toNat →
      readBytes r.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hkeepZero : readBytes r.mem (c.b - 3) 3 = some [0, 0, 0])
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hcall : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r)
    (hreach : ∃ (blk0 : BitVec 64) (position : List Nat) (opened ppar : Bool),
      EscapeReach blk0 xp nxp xcarry count position
        (flagBytes opened ++ flagBytes ppar) (fusedStore c bs73 bs74) r.mem ∧
      position.length ≤ 64) :
    ∃ (env' : Env) (core : State) (c' : FusedCarry) (k : Nat) (len : Nat),
      k ≤ 4 ∧ len ≤ 64 ∧
      (∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction
        (stateAt env s) = runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction
          (stateAt env' core)) ∧
      LoopLatch start xp xn ps bs env' core c.i c' gate 0 ∧
      FrameCarry start xp xn nxp xcarry bs c' (count + len) (pages + 1) ∧
      c'.mem = r.mem ∧
      c'.b = c.b ∧ c'.ent = c.ent ∧ c'.xp = c.xp ∧ c'.nxp = c.nxp ∧
      c'.xcarry = c.xcarry ∧ c'.shr = c.shr ∧
      (∀ j, j < c.shr.toNat →
        readBytes c'.mem (c.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] := by
  obtain ⟨blk0, position, opened, ppar, hreach, hlen⟩ := hreach
  have hi := hinv.index_lt
  have hi' : c.i.toNat < blocksOf bs.length := by omega
  have hwin : FusedWindows c.mem c.b c.shr.toNat c.i (docBlock bs) :=
    fused_windows c.mem c.b c.shr.toNat c.i (docBlock bs) hb3 hi hzero hdoc
  have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
      some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
  have h73 : bs73 = (docBlock bs c.i.toNat).take 32 := by
    obtain ⟨h, _⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
      (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
    rw [hread73] at h
    exact Option.some.inj h
  have h74 : bs74 = (docBlock bs c.i.toNat).drop 32 := by
    obtain ⟨_, h⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
      (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
    rw [hread74] at h
    exact Option.some.inj h
  have hpstep : PageStep bs c bs73 bs74 :=
    { w73 := h73, w74 := h74, store := hstore }
  have hpresentPre : HasBytes (fusedStore c bs73 bs74) c.ent
      (8 * blocksOf bs.length) := by
    show HasBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
      (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) c.ent
        (8 * blocksOf bs.length)
    exact hasBytes_writeBytes hframe.present
  have hprefixPre : EntryPrefix (fusedStore c bs73 bs74) c.ent bs
      (c.i.toNat + 1) :=
    entryPrefix_of_fusedStore hcarry.arrPrefix hpstep.store
  have hstreamPre : StreamPrefix (fusedStore c bs73 bs74) xp xn ps := by
    unfold StreamPrefix
    show readBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
      (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) xp (4 * xn) =
        some (positionsBytes 4 ps)
    rw [fusedValues_arrayidx, readBytes_writeBytes_frame c.mem _
      (c.ent + 8 * c.i.toNat) xp (4 * xn) ?_]
    · exact hcarry.stream
    · rcases hentXp with h | h
      · refine Or.inr ?_
        have h8 : 8 * (c.i.toNat + 1) ≤ 8 * blocksOf bs.length :=
          Nat.mul_le_mul_left 8 (by omega)
        have h8' : 8 * c.i.toNat + 8 ≤ 8 * blocksOf bs.length := by
          simpa [Nat.mul_add, Nat.mul_one] using h8
        calc (c.ent + 8 * c.i.toNat) + 8 = c.ent + (8 * c.i.toNat + 8) := by omega
          _ ≤ c.ent + 8 * blocksOf bs.length := Nat.add_le_add_left h8' c.ent
          _ ≤ xp := h
      · refine Or.inl ?_
        have h4 : 4 * xn ≤ 4 * (xn + 64 * blocksOf bs.length + batchReserve) :=
          Nat.mul_le_mul_left 4 (by omega)
        calc xp + 4 * xn ≤ xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) :=
              Nat.add_le_add_left h4 xp
          _ ≤ c.ent := h
          _ ≤ c.ent + 8 * c.i.toNat := Nat.le_add_right _ _
  have hentXpT : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (count + position.length + batchReserve) ≤ c.ent := by
    rcases hentXp with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have hcap : count + position.length + batchReserve ≤
          xn + 64 * blocksOf bs.length + batchReserve := by omega
      exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hcap) xp) h
  have hkeepXp : nxp + 8 ≤ xp ∨ xp + 4 * blockMax count ≤ nxp := by
    rcases hxpNxp with h | h
    · refine Or.inr ?_
      have hcap : blockMax count ≤ xn + 64 * blocksOf bs.length + batchReserve := by
        unfold blockMax batchReserve
        omega
      exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hcap) xp) h
    · exact Or.inl h
  have hkeepXc : xcarry + 16 ≤ xp ∨ xp + 4 * blockMax count ≤ xcarry := by
    rcases hxpXc with h | h
    · refine Or.inr ?_
      have hcap : blockMax count ≤ xn + 64 * blocksOf bs.length + batchReserve := by
        unfold blockMax batchReserve
        omega
      exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hcap) xp) h
    · exact Or.inl h
  obtain ⟨hkeepPrefix, hkeepStream⟩ :=
    callPage_keeps hreach hpresentPre (by omega) hprefixPre
      (CallChain.count_ge hframe.chain) hstreamPre hentXpT hentNxp hentXc hkeepXp hkeepXc
  rcases BlockEval.bitVec1_eq_zero_or_one
    (fb54Select gate (fusedValues c bs73 bs74).v107) with hdec | hdec
  · -- the DFA arm's escape record
    obtain ⟨h01, h12, h23, h34, hl⟩ :=
      fused_dfa_escape_page sel env s c gate bs73 bs74
        hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
        hinv hshr57 hb3 hgap hread73 hread74 hdec
        hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59 r hcall
    have hcarry' : LoopCarry start xp xn ps bs
        (fusedNext c bs73 bs74
          (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
            hwin.bs58 hwin.bs59).or281 r.mem) :=
      loopCarry_fusedNext hcarry hpstep (by omega) hblocks64 hkeepPrefix hkeepStream
    have hfr' := frameCarry_step (u8k :=
        (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
          hwin.bs58 hwin.bs59).or281) hframe hi' hentXp hentNxp hentXc hcountRoom
      hkeepXp hkeepXc hreach hlen
    exact ⟨_, _, _, 4, position.length, by omega, hlen,
      fun j => runFuel_jump4 h01 h12 h23 h34 j,
      { toFusedLatch := hl, model := hcarry' }, hfr', rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, by simpa only [fusedNext] using hkeepDoc,
      by simpa only [fusedNext] using hkeepZero⟩
  · -- the merge arm's escape record
    obtain ⟨h01, h12, h23, hl⟩ :=
      fused_merge_escape_page sel env s c gate bs73 bs74
        hinv hshr57 hread73 hread74 hdec r hcall
    have hcarry' : LoopCarry start xp xn ps bs
        (fusedNext c bs73 bs74 c.u8k r.mem) :=
      loopCarry_fusedNext hcarry hpstep (by omega) hblocks64 hkeepPrefix hkeepStream
    have hfr' := frameCarry_step (u8k := c.u8k) hframe hi' hentXp hentNxp hentXc
      hcountRoom hkeepXp hkeepXc hreach hlen
    exact ⟨_, _, _, 3, position.length, by omega, hlen,
      fun j => runFuel_jump3 h01 h12 h23 j,
      { toFusedLatch := hl, model := hcarry' }, hfr', rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, by simpa only [fusedNext] using hkeepDoc,
      by simpa only [fusedNext] using hkeepZero⟩

/-! ### The induction

One page per row, the measure `%shr - (%i + 1)`; at zero the latch's test is
true and the run leaves `for.end101` with the page's chain and the model's carry.
The page's record `hreach` is the caller's (the unit's post), and `hkeep` is the
document's preservation, which the record's frame does not restate.  The pages
count one per block, and the peel's page is the one `blocksOf` counts above the
loop's, so `pages + r + 2 ≤ blocks` is maintained across the back edge. -/

/-- **The loop's calling run.**  From the head's invariant, the chain's carry and
the escape record's per-page facts, the run at the escape selection reaches the
bound's exit at `for.end101` in at most five control steps per remaining row plus
five, and the exit carries the model's facts and the chain's. -/
theorem loopRun_frame_aux (sel : Calls) (start : Mem) (xp xn nxp xcarry : Nat)
    (bs : List UInt8)
    (hstoreAll : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < blocksOf bs.length →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat) :
    ∀ (r : Nat) (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
      (count pages : Nat) (ps : List Nat),
      c.shr.toNat - (c.i.toNat + 1) = r →
      pages + r + 2 ≤ blocksOf bs.length →
      blocksOf bs.length = c.shr.toNat + 1 →
      c.shr.toNat < 2 ^ 57 →
      c.shr.toNat ≤ blocksOf bs.length →
      blocksOf bs.length < 2 ^ 64 →
      LoopInv start xp xn ps bs env s c gate 0 →
      FrameCarry start xp xn nxp xcarry bs c count pages →
      3 ≤ c.b →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat →
        readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j)) →
      readBytes c.mem (c.b - 3) 3 = some [0, 0, 0] →
      (c.ent + 8 * blocksOf bs.length ≤ xp ∨
        xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) →
      (c.ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ c.ent) →
      (c.ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ c.ent) →
      (xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
        nxp + 8 ≤ xp) →
      (xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
        xcarry + 16 ≤ xp) →
      (∀ (args : List Value) (mem : Mem) (next : Nat),
        ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) →
      (∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
          (r' : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
        (∀ j, j < c'.shr.toNat →
          readBytes r'.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
        readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0]) →
      (∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
          (r' : CallOutcome) (xnA : Nat),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
        ∃ (blk0 : BitVec 64) (position : List Nat) (opened ppar : Bool),
          EscapeReach blk0 xp nxp xcarry xnA position
            (flagBytes opened ++ flagBytes ppar) mem r'.mem ∧
          position.length ≤ 64) →
      ∃ (env' : Env) (e : State) (c' : FusedCarry) (count' pages' : Nat) (j : Nat),
        j ≤ 5 * r + 5 ∧
        FusedExit env' e c' ∧
        LoopCarry start xp xn ps bs c' ∧
        FrameCarry start xp xn nxp xcarry bs c' count' pages' ∧
        pages' + 1 ≤ blocksOf bs.length ∧
        c'.i.toNat + 1 = blocksOf bs.length ∧
        (∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction
          (stateAt env s) = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e)
  | 0, env, s, c, gate, count, pages, ps, hmeasure, hpages, hblocks, hshr57,
    hshrLe, hblocks64, hinv, hframe, hb3, hgap, hdoc, hzero, hentXp, hentNxp,
    hentXc, hxpNxp, hxpXc, hcallAll, hkeep, hreachAll => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hi' : c.i.toNat < blocksOf bs.length := by omega
      have hsuccT : (c.i + 1).toNat = c.i.toNat + 1 :=
        toNat_succ_of_lt (by omega)
      have hbound : c.i + 1 = c.shr := by
        apply BitVec.eq_of_toNat_eq
        rw [hsuccT]
        omega
      have hcshr : (c.i + 1).toNat = c.shr.toNat := congrArg BitVec.toNat hbound
      have hcountRoom : count + 64 ≤ xn + 64 * blocksOf bs.length := by
        have hcle := hframe.chain.count_le
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
          some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ :=
        readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hcCall⟩ := hcallAll _ _ _
      obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep c _ _ _ _ _ _ rc hcCall
      obtain ⟨blk0, position, opened, ppar, hreach, hlen⟩ :=
        hreachAll c _ _ _ _ _ _ rc count hcCall
      obtain ⟨env', core, c', k, len, hk, hlen', hrun, hl, hfr', hmem', hb', he',
        hxp', hnxp', hxc', hshr', hdoc', hzero'⟩ :=
        loopPage_zero sel env s c gate ((docBlock bs c.i.toNat).take 32)
          ((docBlock bs c.i.toNat).drop 32) start xp xn nxp xcarry bs ps count
          pages rc hinv.toFusedInv hinv.model hframe
          (hstoreAll c ((docBlock bs c.i.toNat).take 32)
            ((docBlock bs c.i.toNat).drop 32) hi'
            hread73 hread74)
          hshr57 hb3 hshrLe
          hblocks64 hgap hdoc hzero hentXp hentNxp hentXc hxpNxp hxpXc hcountRoom
          hkeepDoc hkeepZero hread73 hread74 hcCall
          ⟨blk0, position, opened, ppar, hreach, hlen⟩
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 1 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).1.mpr hbound
      obtain ⟨hstep, hexit⟩ :=
        fused_latch_exit sel env' core c.i c' gate 0 hl.toFusedLatch hbit
      have hsuccBlocks : c'.i.toNat + 1 = blocksOf bs.length := by
        rw [hl.succ, hcshr, ← hblocks]
      refine ⟨ifEnd98Env env' c.i c'.shr,
        stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" },
        c', count + len, pages + 1, k + 1, by omega, hexit, hl.model, hfr',
        by omega, hsuccBlocks, fun j => ?_⟩
      rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
        runFuel_jump_prefix hstep j]
  | r + 1, env, s, c, gate, count, pages, ps, hmeasure, hpages, hblocks, hshr57,
    hshrLe, hblocks64, hinv, hframe, hb3, hgap, hdoc, hzero, hentXp, hentNxp,
    hentXc, hxpNxp, hxpXc, hcallAll, hkeep, hreachAll => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hi' : c.i.toNat < blocksOf bs.length := by omega
      have hsuccT : (c.i + 1).toNat = c.i.toNat + 1 :=
        toNat_succ_of_lt (by omega)
      have hne : c.i + 1 ≠ c.shr := by
        intro heq
        have hcongr := congrArg BitVec.toNat heq
        rw [hsuccT] at hcongr
        omega
      have hcountRoom : count + 64 ≤ xn + 64 * blocksOf bs.length := by
        have hcle := hframe.chain.count_le
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
          some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ :=
        readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hcCall⟩ := hcallAll _ _ _
      obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep c _ _ _ _ _ _ rc hcCall
      obtain ⟨blk0, position, opened, ppar, hreach, hlen⟩ :=
        hreachAll c _ _ _ _ _ _ rc count hcCall
      obtain ⟨env', core, c', k, len, hk, hlen', hrun, hl, hfr', hmem', hb', he',
        hxp', hnxp', hxc', hshr', hdoc', hzero'⟩ :=
        loopPage_zero sel env s c gate ((docBlock bs c.i.toNat).take 32)
          ((docBlock bs c.i.toNat).drop 32) start xp xn nxp xcarry bs ps count
          pages rc hinv.toFusedInv hinv.model hframe
          (hstoreAll c ((docBlock bs c.i.toNat).take 32)
            ((docBlock bs c.i.toNat).drop 32) hi'
            hread73 hread74)
          hshr57 hb3 hshrLe
          hblocks64 hgap hdoc hzero hentXp hentNxp hentXc hxpNxp hxpXc hcountRoom
          hkeepDoc hkeepZero hread73 hread74 hcCall
          ⟨blk0, position, opened, ppar, hreach, hlen⟩
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 0 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).2.mpr hne
      obtain ⟨hstep, hinv'⟩ :=
        fused_latch_loop sel env' core c.i c' gate 0 hl.toFusedLatch hbit
          (by rw [hshr']; exact hshr57)
      have hmeasure' : c'.shr.toNat - (c'.i.toNat + 1) = r := by
        rw [hshr', hl.succ, hsuccT]
        omega
      have hpages' : pages + 1 + r + 2 ≤ blocksOf bs.length := by omega
      have hshrLe' : c'.shr.toNat ≤ blocksOf bs.length := by rw [hshr']; exact hshrLe
      have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
        rw [hb', he', hshr']; exact hgap
      have hb3' : 3 ≤ c'.b := by rw [hb']; exact hb3
      have hentXp' : c'.ent + 8 * blocksOf bs.length ≤ xp ∨
          xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c'.ent := by
        rw [he']; exact hentXp
      have hentNxp' : c'.ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ c'.ent := by
        rw [he']; exact hentNxp
      have hentXc' : c'.ent + 8 * blocksOf bs.length ≤ xcarry ∨
          xcarry + 16 ≤ c'.ent := by
        rw [he']; exact hentXc
      obtain ⟨env'', e', c'', count', pages', j, hjle, hexit', hcarry', hfr'',
        hpages'', hsucc'', hrun'⟩ :=
        loopRun_frame_aux sel start xp xn nxp xcarry bs hstoreAll r
          (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.body54", pre := some "if.end98" })
          c' gate (count + len) (pages + 1)
          ps hmeasure' hpages'
          (by rw [hshr']; exact hblocks) (by rw [hshr']; exact hshr57) hshrLe' hblocks64
          { toFusedInv := hinv', model := hl.model } hfr' hb3' hgap'
          (by
            intro j' hj'
            rw [hshr'] at hj'
            rw [hb']
            exact hdoc' j' hj')
          (by rw [hb']; exact hzero') hentXp' hentNxp' hentXc' hxpNxp hxpXc
          hcallAll hkeep hreachAll
      refine ⟨env'', e', c'', count', pages', k + 1 + j, by omega, hexit', hcarry',
        hfr'', hpages'', hsucc'', fun k' => ?_⟩
      rw [show k + 1 + j + k' = k + (1 + (j + k')) from by omega,
        hrun (1 + (j + k')), runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'

/-- **The loop's calling run from the head.**  The auxiliary form at the head's
own measure, `%shr - (%i + 1)` rows to go, with the caller's staging as the
chain's first node. -/
theorem loopRun_frame (sel : Calls) (start : Mem) (xp xn nxp xcarry : Nat)
    (bs : List UInt8)
    (hstoreAll : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < blocksOf bs.length →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat)
    (env : Env) (s : State)
    (c : FusedCarry) (gate : BitVec 1) (ps : List Nat)
    (hstart : c.mem = start)
    (hblocks : blocksOf bs.length = c.shr.toNat + 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hinv : LoopInv start xp xn ps bs env s c gate 0)
    (hcount0 : readBytes c.mem nxp 8 = some (wordBytes 8 xn))
    (hstream0 : StreamPrefix c.mem xp xn ps)
    (hpresent0 : HasBytes c.mem c.ent (8 * blocksOf bs.length))
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hentNxp : c.ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ c.ent)
    (hentXc : c.ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ c.ent)
    (hxpNxp : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
      nxp + 8 ≤ xp)
    (hxpXc : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
      xcarry + 16 ≤ xp)
    (hcallAll : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem)
        (next : Nat) (r' : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
      (∀ j, j < c'.shr.toNat →
        readBytes r'.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0])
    (hreachAll : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem)
        (next : Nat) (r' : CallOutcome) (xnA : Nat),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
      ∃ (blk0 : BitVec 64) (position : List Nat) (opened ppar : Bool),
        EscapeReach blk0 xp nxp xcarry xnA position
          (flagBytes opened ++ flagBytes ppar) mem r'.mem ∧
        position.length ≤ 64) :
    ∃ (env' : Env) (e : State) (c' : FusedCarry) (count pages : Nat) (j : Nat),
      j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      FusedExit env' e c' ∧
      RunFrame start xp xn nxp xcarry ps bs c' count pages ∧
      (∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction
        (stateAt env s) = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e) := by
  have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
  have hnil : CallChain c.ent (blocksOf bs.length) xp nxp xcarry xn start c.mem xn 0 := by
    rw [hstart]
    exact CallChain.nil
  have hframe0 : FrameCarry start xp xn nxp xcarry bs c xn 0 :=
    { chain := hnil
      countRead := hcount0
      stream := ⟨ps, hstream0⟩
      present := hpresent0 }
  have hpages0 : 0 + (c.shr.toNat - (c.i.toNat + 1)) + 2 ≤ blocksOf bs.length := by
    omega
  obtain ⟨env', e, c', count, pages, j, hj, hexit, hcarry, hfr, hpages, hsucc, hrun⟩ :=
    loopRun_frame_aux sel start xp xn nxp xcarry bs hstoreAll
      (c.shr.toNat - (c.i.toNat + 1)) env s c gate xn 0 ps rfl hpages0 hblocks
      hshr57 hshrLe hblocks64 hinv hframe0 hb3 hgap hdoc hzero hentXp hentNxp
      hentXc hxpNxp hxpXc hcallAll hkeep hreachAll
  exact ⟨env', e, c', count, pages, j, hj, hexit,
    { carry := hcarry, frame := hfr, succ := hsucc, pagesLe := hpages }, hrun⟩

/-! ### The exit's three facts

The bundle's fields in the shapes `callTail_of_chain` names them. -/

/-- **The count the peel's slot holds.**  The chain records it at the pages'
count; this is `callTail_of_chain`'s `hcountL`. -/
theorem count_slot_read {start : Mem} {xp xn nxp xcarry : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {count pages : Nat}
    (h : RunFrame start xp xn nxp xcarry ps bs c count pages) :
    readBytes c.mem nxp 8 = some (wordBytes 8 count) :=
  h.frame.countRead

/-- **The stream's prefix at the pages' count.**  The pages' own writes; this is
`callTail_of_chain`'s `hstream`. -/
theorem stream_prefix_at_exit {start : Mem} {xp xn nxp xcarry : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {count pages : Nat}
    (h : RunFrame start xp xn nxp xcarry ps bs c count pages) :
    ∃ ps0 : List Nat, readBytes c.mem xp (4 * count) = some (positionsBytes 4 ps0) :=
  h.frame.stream

/-- **The entry array's presence at the run's memory.**  The staging's presence,
carried through the pages' stores and calls; this is the `hpresent` premise
`callPage_keeps` reads. -/
theorem array_present_at_exit {start : Mem} {xp xn nxp xcarry : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {count pages : Nat}
    (h : RunFrame start xp xn nxp xcarry ps bs c count pages) :
    HasBytes c.mem c.ent (8 * blocksOf bs.length) :=
  h.frame.present

/-- **The run's own frame.**  The chain's fold at the exit: every byte outside
the four regions the pages' stores and calls name is the caller's.  This is
`CallChain.frame` read at the bundle's end, the fact `LoopCarry`'s one-region
`EntryFrame` cannot state on a run whose pages call. -/
theorem runFrame_writeRegions {start : Mem} {xp xn nxp xcarry : Nat}
    {ps : List Nat} {bs : List UInt8} {c : FusedCarry} {count pages : Nat}
    (h : RunFrame start xp xn nxp xcarry ps bs c count pages) :
    UnchangedOutside start c.mem
      (escapeCallWriteRegions c.ent (blocksOf bs.length) xp nxp xcarry count) :=
  h.frame.chain.frame

/-- **The tail's third disjunct.**  From the run's exit bundle and the peel's own
reach, `S1BlocksTail`'s calling shape holds: the four-region frame the pages
composed, the array's prefix at the peel's index, the count the peel's slot holds,
the stream's prefix and the peel's escape record. -/
theorem tail_third_of_frame {start : Mem} {xp xn nxp xcarry : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {count pages : Nat} {arm : BitVec 64}
    {M : Mem} {shr : Nat} {or135 andv w blk0 : BitVec 64}
    {position : List Nat} {opened ppar : Bool}
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hreach : EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) M)
    (hlen : position.length ≤ 64)
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    S1BlocksTail start c.ent xp nxp xcarry xn arm bs M := by
  obtain ⟨ps0, hps0⟩ := hrun.frame.stream
  exact callTail_of_chain hrun.carry hrun.frame.chain hrun.pagesLe hrun.succ
    hshr hor hshrEq hand hw harm hrun.frame.countRead hreach hps0 hlen hxpSep

/-! ### Axiom footprints

`FrameCarry` is stated by nothing; `RunFrame`, `CallChain.count_ge`,
`callPage_present`, `count_slot_read`, `stream_prefix_at_exit` and
`array_present_at_exit` are structure projections and the region/read algebra of
`JsonS1BlocksEscapeRun` and `JsonS1BlocksRecordFrame`, and carry `propext` and
`Quot.sound` only.  `Classical.choice` accompanies the store arithmetic `omega`
discharges and the chain's fold (`frameCarry_step`, `loopPage_zero`,
`loopRun_frame_aux`, `loopRun_frame`, `runFrame_writeRegions`,
`tail_third_of_frame`) — the same carrier `JsonS1BlocksRecordFrame` reports for
its store and frame statements.  No statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.FrameCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.RunFrame
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.CallChain.count_ge
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.callPage_present
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.frameCarry_step
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.loopPage_zero
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.loopRun_frame_aux
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.loopRun_frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.runFrame_writeRegions
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.count_slot_read
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.stream_prefix_at_exit
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.array_present_at_exit
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunFrame.tail_third_of_frame

end LeanLLVM.Refinement.JsonS1BlocksRunFrame
