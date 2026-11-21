/-
The loop's run residual: the carry the induction hands the tail, and the charged
prefix at the record's budget.

`JsonS1BlocksLoopFacts` states the tail's loop facts at a carry (`LoopExitFacts`,
`tail_peel_facts`) but the loop's own induction does not carry them: the four
page shapes `JsonS1BlocksLoop.fusedInv_page` composes are stated only at
`FusedInv`/`FusedLatch`, so nothing in the tree produces `EntryPrefix`,
`StreamPrefix`, the ASCII carry or the accumulator carry at `for.end101`.  This
module adds, beside `FusedInv`, the carry facts as an invariant, proves the four
page shapes preserve it, and derives the exit facts and the tail's memory shape
from it.

## The invariant

* **`LoopCarry`** — the model-side carry at one loop head: the entry array's
  prefix at the loop's index (`EntryPrefix`), the ASCII word at the byte fold
  (`asciiAcc`), its lane count, the entry stream's prefix, and the index inside
  the document's block count.  It is the part of `LoopExitFacts` the pages
  preserve, plus the stream prefix and the block bound.  Two of `LoopExitFacts`'
  fields are *not* here: the run's own frame (`EntryFrame mem0 c.mem`) is a
  whole-run fact, since a page that takes the escape call writes the stream, and
  the accumulator's fold and length are the two arms' own arithmetic, which no
  module in the tree states.  The exit theorems take those three as the run's
  obligations.
* **`LoopInv`** — `FusedInv` together with the carry; **`LoopLatch`** — the
  same at the back edge.  **`LoopTerm`** — the exit terminal with the carry.
* **`PageStep`** — one page's model identities: the two document windows and
  the stored word (`fusedValues.or84 = stage1Word`).
* **`PageModel`** — the store-word identity, quantified over the carry so the
  induction can use it at every page.

## What is proved

* `loopCarry_fusedNext` — one page's carry step: the ASCII word advances by
  `ascii_of_fusedAscii`, the prefix and stream come from the page's memory, and
  the lane count is the successor's.
* `loopCarry_store` — the skip page's memory: the store appends the model's slot
  (`entryPrefix_of_fusedStore`) and the stream's prefix reads through it at the
  staging's separation (`readBytes_writeBytes_frame`).
* `loopFrame_store` — the frame's page step: the page's store is inside the
  entry array (`entryFrame_of_fusedStore`), so the run's own frame is composed
  from the store pages.  A page that calls also writes the stream, so the frame
  is a whole-run fact and the exit theorems take it, not the invariant.
* `loopLatch_page` — **the four page shapes**, DFA-escape, DFA-skip,
  merge-escape and merge-skip: each reaches the back edge with `LoopLatch` (the
  latch invariant plus the successor's carry), using `fused_windows` for the six
  row windows and the page lemmas' own `FusedLatch`.
* `loopRun_carry` — the induction, one page per row, carrying `LoopCarry` to
  `for.end101`; the terminal is `LoopTerm`.
* `loopExitFacts_at`, `loopExit_array_full`, `loopExit_peel_slot`,
  `loopExit_staging` — the exit facts at `FusedExit`: `LoopExitFacts`,
  `EntryPrefix` at the whole block count as one read (`stage1Words`), the peel's
  slot as the model's word (`peel_slot_of_model`), and the staging
  (`staging_of_exitFacts`).
* `tail_facts_of_exitCarry`, `tail_peel_facts_of_exitCarry` — the tail's three
  loop facts at the peel, and the array's full read.  `tail_aligned_of_carry` and
  `tail_peel_of_carry` are the committed `S1BlocksTail`'s first two disjuncts at
  the carry; its third, the peel's escape call, is the escape unit's
  `EscapeReach`, which this module does not stage
  (`JsonS1BlocksEscapeRun.callTail_of_chain`).
* `onePrefix_of_exit` — the committed one-prefix (`s1BlocksPrefix_exit`) read as
  a `OnePrefix`; its fuel is not exposed there, so the bound is the residual.
* `s1BlocksInit_entryState`, `s1BlocksRun_at_budget`,
  `s1BlocksBudget_of_phaseCharge` — the run at `s1BlocksBudget`: `s1BlocksInit`
  is `EntryState` at `next = 1`, the one-prefix's fuel composed with the exit's
  run, and the entry's charge arithmetic at the record's own budget term.

## What remains

The residual is three kinds of input, and none is a restatement of a committed
conclusion:

* **The page's word identity's inputs.**  `PageModel` is proved in
  `JsonS1BlocksPageModel`, which closes the store word
  (`(fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat`) with the
  `WordIdentities`/`PeelWord` docBlock corollary.  What the induction still takes
  is the identity's three inputs at every head: the carried classifier state
  (`PageCarry`), the whole-block bound (`64 * %shr ≤ bs.length`, true of the
  entry's `%shr = n >>> 6`), and the two windows being the block's halves (the
  run's read tie).
* **The accumulator's fold and length** at the exit
  (`packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat)`, `c.u8k.length = 4`).
  The loop's two arms hand on different words — the DFA arm's mask and the merge
  arm's carried one — so the fold between them is the staging's carry, not the
  invariant's; `JsonS1BlocksLoopFacts`'s header names this step too.
* **The escape call's keeps** at the calling page: the call keeps the entry
  array read (its prefix at the successor index) and the stream's prefix.  The
  record's frame gives the call's own regions
  (`JsonS1BlocksCompose.if_then150_escape_keepsEntry` reads the array back through
  them), and the invariant's stream prefix is below the call's cursor, so these
  are the caller's staging facts the induction reads, in the shape
  `fusedInv_step` already reads its `hkeep`.
* **The run's own frame**, taken by the exit theorems.  `EntryFrame mem0 c.mem`
  is the loop's own store frame; a page that calls writes the stream, so the
  frame is not per page.  The record's composed frame is the four-region one
  (`escapeCallWriteRegions`), and the count that threads its widths is the
  remaining composition.  The loop's escape bit is `%tobool95.not`, i.e.
  `arm &&& 2 = 0`, and the page that *calls* is the one whose bit is `0`, so on
  `arm &&& 2 ≠ 0` every page calls and the run's memory is not the caller's
  outside the array.  The one-region frame `tail_aligned_of_carry` and
  `tail_peel_of_carry` instantiate is then the calling-free configuration
  (`arm &&& 2 = 0`, where the loop's bit is the skip arm), which is the first two
  disjuncts'; the third disjunct is stated at the four-region frame at the count
  the pages left, and `JsonS1BlocksEscapeRun.callTail_of_chain` supplies it from
  the same carry plus the pages' chain.
-/
import LeanLLVM.Refinement.JsonS1BlocksLoopFacts
import LeanLLVM.Refinement.JsonS1BlocksSatisfies
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonS1BlocksPrefix
import LeanLLVM.Refinement.JsonS1BlocksStream

namespace LeanLLVM.Refinement.JsonS1BlocksLoopRun

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksStream
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The carry and the invariant

The loop's model-side carry at one head.  It is the part of `LoopExitFacts` the
pages preserve — the array's prefix, the ASCII fold and its lane count — read at
the loop's index rather than at the exit, plus the stream's prefix and the
document bound the pages need.  The frame and the accumulator are the run's own,
stated at the exit. -/

/-- **The loop's carry at one head.** -/
structure LoopCarry (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (c : FusedCarry) : Prop where
  /-- The array's prefix: one model word per block the loop passed. -/
  arrPrefix : EntryPrefix c.mem c.ent bs c.i.toNat
  /-- The ASCII word at the byte fold. -/
  ascii : packLanes c.ascii = bytesToNat (asciiAcc bs c.i.toNat)
  /-- The ASCII word has four lanes. -/
  ascLen : c.ascii.length = 4
  /-- The entry stream's prefix, below every call's cursor. -/
  stream : StreamPrefix c.mem xp xn ps
  /-- The index is inside the document's block count. -/
  inside : c.i.toNat ≤ blocksOf bs.length

/-- The carry's exit shape: `LoopExitFacts`, once the run's own frame and the
accumulator's fold and length are at hand.  The accumulator is not part of the
invariant: the loop's two arms hand on different words (the DFA arm's mask, the
merge arm's carried one), and the fold identity between them is the loop's own
arithmetic, which no module in the tree states. -/
theorem LoopCarry.toLoopExitFacts {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} (h : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : c.u8k.length = 4) :
    LoopExitFacts mem0 bs c :=
  { arrPrefix := h.arrPrefix
    arrFrame := hframe
    arrAscii := h.ascii
    arrU8k := hu8k
    ascLen := h.ascLen
    accLen := haccLen }

/-- **The loop head's invariant**: the page invariant and the carry. -/
structure LoopInv (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (env : Env) (s : State) (c : FusedCarry) (gate esc : BitVec 1) : Prop
    extends FusedInv env s c gate esc where
  /-- The model-side carry. -/
  model : LoopCarry mem0 xp xn ps bs c

/-- **The back edge's invariant**: the latch's invariant and the carry. -/
structure LoopLatch (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (env : Env) (s : State) (i : BitVec 64) (c : FusedCarry) (gate esc : BitVec 1) :
    Prop extends FusedLatch env s i c gate esc where
  /-- The model-side carry. -/
  model : LoopCarry mem0 xp xn ps bs c

/-- The loop's terminal: `for.end101` with the exit's facts and the carry. -/
inductive LoopTerm (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8) :
    State → Prop where
  | exit (env : Env) (s : State) (c : FusedCarry) :
      FusedExit env s c → LoopCarry mem0 xp xn ps bs c →
      LoopTerm mem0 xp xn ps bs (stateAt env s)

/-- Every carry-carrying loop terminal is the loop's own terminal. -/
theorem LoopTerm.toTerm {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {e : State} (h : LoopTerm mem0 xp xn ps bs e) :
    FusedTerm e := by
  rcases h with ⟨env, s, c, hexit, -⟩
  exact FusedTerm.exit env s c hexit

/-- **One page's model identities.**  The two document windows and the stored
word: the page's own values are the block's halves and the model's entry word. -/
structure PageStep (bs : List UInt8) (c : FusedCarry) (bs73 bs74 : List UInt8) :
    Prop where
  /-- The first loaded word is the block's first half. -/
  w73 : bs73 = (docBlock bs c.i.toNat).take 32
  /-- The second loaded word is the block's second half. -/
  w74 : bs74 = (docBlock bs c.i.toNat).drop 32
  /-- The stored word is the model's entry word. -/
  store : (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat

/-- **The classifier's carry, in the model's spelling.**  The fast tables read
the block's halves and the loop's three carried state words, and the entry word
of the specification is the model's word at the block's class carry.  These are
the facts that tie the loop's carried state to that model, and they are the
loop's own residual: no module derives the DFA state words from the classifier's
carry.  `pageCtx` is the model's `Ctx` at the block, with the run's open and
parity bits chosen from its own odd-run bit (the entry word reads neither). -/
def pageCtx (bs : List UInt8) (i : Nat) : LeanLLVM.Refinement.JsonS1MasksIR.Ctx :=
  { p := 0
    c := 0
    o := 0
    lo := blockLo (padded bs) i
    hi := blockHi (padded bs) i
    st := classCarryAt (padded bs) ⟨false, false⟩ (64 * i)
    opened := (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)).oddRun
    ppar := true }

/-- **The carried state at one head**, as the page's entry word reads it: the
two-state escaped-quote word, the seed lane and the shift register. -/
structure PageCarry (bs : List UInt8) (c : FusedCarry) : Prop where
  /-- The escaped-quote word is the model's `%esc.and00` at the block. -/
  and00 : c.st0 &&& c.st9 = LeanLLVM.Refinement.JsonS1MasksSteps.escAnd00W
    (pageCtx bs c.i.toNat)
  /-- The third state word is the model's seed lane. -/
  st15 : c.st15 = LeanLLVM.Refinement.JsonS1MasksSteps.seedW (pageCtx bs c.i.toNat)
  /-- The shift register is the previous block's top scalar lane. -/
  prevS : c.prevS = (if stage1PrevS bs c.i.toNat then 1 else 0)

/-- **The page's word identity, at every full block.**  The stored word is the
model's entry word at the page's own index — the fast-table classifier against
the specification's six masks, at `for.body54`'s registers.  The page processes
a whole block, so the model's tail clamp is the all-ones word; the two loaded
words are the block's halves, which the run reads out of the document window;
and the carried state is `PageCarry`'s.  The block's window is `docBlock`'s. -/
structure PageModel (bs : List UInt8) : Prop where
  /-- The page's stored word is the model's entry word. -/
  storeW : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
    64 * (c.i.toNat + 1) ≤ bs.length →
    PageCarry bs c →
    bs73 = (docBlock bs c.i.toNat).take 32 →
    bs74 = (docBlock bs c.i.toNat).drop 32 →
    (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat

/-! ### One page's carry step -/

/-- The successor index's `toNat`, below the word's capacity. -/
theorem toNat_succ_of_lt {i : BitVec 64} (h : i.toNat + 1 < 2 ^ 64) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
  exact Nat.mod_eq_of_lt h

/-- **One page advances the carry.**  Given the page's identities and the
page's memory's prefix and stream prefix, the successor carry holds: the ASCII
word at the next fold is `ascii_of_fusedAscii`, the accumulator is the page's,
and the lengths are the successor's. -/
theorem loopCarry_fusedNext {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {bs73 bs74 : List UInt8}
    {u8k : List (BitVec 64)} {mem : Mem}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hp : PageStep bs c bs73 bs74)
    (hnext : c.i.toNat + 1 ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hprefix : EntryPrefix mem c.ent bs (c.i.toNat + 1))
    (hstream : StreamPrefix mem xp xn ps) :
    LoopCarry mem0 xp xn ps bs (fusedNext c bs73 bs74 u8k mem) := by
  have hi : c.i.toNat < blocksOf bs.length := by omega
  have hsucc : (fusedNext c bs73 bs74 u8k mem).i.toNat = c.i.toNat + 1 := by
    show (c.i + 1).toNat = c.i.toNat + 1
    exact toNat_succ_of_lt (by omega)
  refine
    { arrPrefix := ?_
      ascii := ?_
      ascLen := fusedNext_ascii_length c bs73 bs74 u8k mem hc.ascLen
      stream := ?_
      inside := ?_ }
  · show EntryPrefix (fusedNext c bs73 bs74 u8k mem).mem
      (fusedNext c bs73 bs74 u8k mem).ent bs (fusedNext c bs73 bs74 u8k mem).i.toNat
    rw [hsucc]
    exact hprefix
  · show packLanes (fusedNext c bs73 bs74 u8k mem).ascii =
      bytesToNat (asciiAcc bs (fusedNext c bs73 bs74 u8k mem).i.toNat)
    rw [hsucc]
    exact ascii_of_fusedAscii hi hp.w73 hp.w74 hc.ascLen hc.ascii
  · show StreamPrefix (fusedNext c bs73 bs74 u8k mem).mem xp xn ps
    exact hstream
  · show (fusedNext c bs73 bs74 u8k mem).i.toNat ≤ blocksOf bs.length
    rw [hsucc]
    exact hnext

/-- **The skip page's memory.**  The store appends the model's slot, the loop's
frame survives it, and the stream's prefix reads through it: the store is inside
the entry array, which the staging separates from the stream's base. -/
theorem loopCarry_store {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {bs73 bs74 : List UInt8}
    {u8k : List (BitVec 64)}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hp : PageStep bs c bs73 bs74)
    (hnext : c.i.toNat + 1 ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    LoopCarry mem0 xp xn ps bs
      (fusedNext c bs73 bs74 u8k (fusedStore c bs73 bs74)) := by
  have hi : c.i.toNat < blocksOf bs.length := by omega
  have hstream : StreamPrefix (fusedStore c bs73 bs74) xp xn ps := by
    have hread : readBytes (fusedStore c bs73 bs74) xp (4 * xn) =
        readBytes c.mem xp (4 * xn) := by
      show readBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
        (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) xp (4 * xn) =
          readBytes c.mem xp (4 * xn)
      rw [fusedValues_arrayidx]
      refine readBytes_writeBytes_frame c.mem _ _ xp (4 * xn) ?_
      rcases hentXp with h | h
      · exact Or.inr (by rw [natToBytes_length]; omega)
      · exact Or.inl (by omega)
    unfold StreamPrefix at *
    rw [hread]
    exact hc.stream
  exact loopCarry_fusedNext hc hp hnext hblocks64
    (entryPrefix_of_fusedStore hc.arrPrefix hp.store) hstream

/-- **The frame's page step.**  The page's store is inside the entry array, so
the run's frame over the array survives it.  This is the page step of the frame;
the frame is not a `LoopCarry` field, because a page that takes the escape call
writes the stream, so the exit facts take the run's frame as the caller's
obligation. -/
theorem loopFrame_store {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    {bs73 bs74 : List UInt8}
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hi : c.i.toNat < blocksOf bs.length) :
    EntryFrame mem0 (fusedStore c bs73 bs74) c.ent (blocksOf bs.length) :=
  entryFrame_of_fusedStore hframe hi

/-- **The frame composes with the peel's store.**  The peel's store is inside
the array too, so the run's frame and the peel's store are the tail's frame. -/
theorem loopFrame_peel {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    {w : BitVec 64}
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hsucc : c.i.toNat + 1 = blocksOf bs.length) :
    EntryFrame mem0 (writeBytes c.mem (c.ent + 8 * c.i.toNat)
      (natToBytes w.toNat 8)) c.ent (blocksOf bs.length) :=
  peelStore_frame hframe hsucc (natToBytes_length w.toNat 8)

/-! ### The four page shapes

`fusedInv_page`'s four arms, each reaching the latch with the carry.  The
document's blocks are read at the page's own address, so the two loaded words
are the block's halves (`readBytes_split`), which is what `PageStep` needs; the
six row windows are `fused_windows`' at the page's index. -/

/-- **One page, with the carry.**  From the head's invariant the page reaches the
latch at the successor's carry, in at most four control steps, on whichever of
the four shapes the two decisions select: DFA-escape, DFA-skip, merge-escape or
merge-skip.  The document survives the page (the store above it, the call's own
keeps), so the next page reads what this one read. -/
theorem loopLatch_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (bs73 bs74 : List UInt8)
    (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (hinv : FusedInv env s c gate escBit)
    (hcarry : LoopCarry mem0 xp xn ps bs c)
    (hmodel : PageModel bs)
    (hstate : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length)
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
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (r : CallOutcome)
    (hcall : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r)
    (hkeepDoc : ∀ j, j < c.shr.toNat →
      readBytes r.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hkeepZero : readBytes r.mem (c.b - 3) 3 = some [0, 0, 0])
    (hkeepPrefix : EntryPrefix r.mem c.ent bs (c.i.toNat + 1))
    (hkeepStream : StreamPrefix r.mem xp xn ps) :
    ∃ (env' : Env) (core : State) (c' : FusedCarry) (k : Nat),
      k ≤ 4 ∧
      (∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction (stateAt env s)
        = runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt env' core)) ∧
      LoopLatch mem0 xp xn ps bs env' core c.i c' gate escBit ∧
      c'.b = c.b ∧ c'.ent = c.ent ∧ c'.xp = c.xp ∧ c'.nxp = c.nxp ∧
      c'.xcarry = c.xcarry ∧ c'.shr = c.shr ∧
      (∀ j, j < c.shr.toNat →
        readBytes c'.mem (c.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] := by
  have hi := hinv.index_lt
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
  rcases BlockEval.bitVec1_eq_zero_or_one
    (fb54Select gate (fusedValues c bs73 bs74).v107) with hdec | hdec
  · -- the DFA arm
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · -- DFA, escape record: the page stores, then calls
      subst he
      obtain ⟨h01, h12, h23, h34, hl⟩ :=
        fused_dfa_escape_page sel env s c gate bs73 bs74
          hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
          hinv hshr57 hb3 hgap hread73 hread74 hdec
          hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59 r hcall
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74
            (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
              hwin.bs58 hwin.bs59).or281 r.mem) :=
        loopCarry_fusedNext hcarry
          { w73 := h73, w74 := h74
            store := hmodel.storeW c bs73 bs74 (by omega) (hstate c hi) h73 h74 }
          (by omega) hblocks64 hkeepPrefix hkeepStream
      exact ⟨_, _, _, 4, by omega, fun j => runFuel_jump4 h01 h12 h23 h34 j,
        { toFusedLatch := hl, model := hcarry' }, rfl, rfl, rfl, rfl, rfl, rfl,
        hkeepDoc, hkeepZero⟩
    · -- DFA, skip the record
      subst he
      obtain ⟨h01, h12, h23, hl⟩ :=
        fused_dfa_skip_page sel env s c gate bs73 bs74
          hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
          hinv hshr57 hb3 hgap hread73 hread74 hdec
          hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74
            (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
              hwin.bs58 hwin.bs59).or281 (fusedStore c bs73 bs74)) :=
        loopCarry_store hcarry
          { w73 := h73, w74 := h74
            store := hmodel.storeW c bs73 bs74 (by omega) (hstate c hi) h73 h74 }
          (by omega) hblocks64 hentXp
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 (docBlock bs) hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨_, _, _, 3, by omega, fun j => runFuel_jump3 h01 h12 h23 j,
        { toFusedLatch := hl, model := hcarry' }, rfl, rfl, rfl, rfl, rfl, rfl,
        hdoc', hzero'⟩
  · -- the merge
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · -- merge, escape record
      subst he
      obtain ⟨h01, h12, h23, hl⟩ :=
        fused_merge_escape_page sel env s c gate bs73 bs74
          hinv hshr57 hread73 hread74 hdec r hcall
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74 c.u8k r.mem) :=
        loopCarry_fusedNext hcarry
          { w73 := h73, w74 := h74
            store := hmodel.storeW c bs73 bs74 (by omega) (hstate c hi) h73 h74 }
          (by omega) hblocks64 hkeepPrefix hkeepStream
      exact ⟨_, _, _, 3, by omega, fun j => runFuel_jump3 h01 h12 h23 j,
        { toFusedLatch := hl, model := hcarry' }, rfl, rfl, rfl, rfl, rfl, rfl,
        hkeepDoc, hkeepZero⟩
    · -- merge, skip the record
      subst he
      obtain ⟨h01, h12, hl⟩ :=
        fused_merge_skip_page sel env s c gate bs73 bs74
          hinv hshr57 hread73 hread74 hdec
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74 c.u8k (fusedStore c bs73 bs74)) :=
        loopCarry_store hcarry
          { w73 := h73, w74 := h74
            store := hmodel.storeW c bs73 bs74 (by omega) (hstate c hi) h73 h74 }
          (by omega) hblocks64 hentXp
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 (docBlock bs) hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨_, _, _, 2, by omega, fun j => runFuel_jump2 h01 h12 j,
        { toFusedLatch := hl, model := hcarry' }, rfl, rfl, rfl, rfl, rfl, rfl,
        hdoc', hzero'⟩

/-! ### The induction

The measure is the distance to the bound, one page per row.  At zero the latch's
test is true and the run leaves `for.end101` with the successor's carry; above
zero it is false, the back edge re-enters the head, and the page's own document
and zeroes are the next page's.  The page is `loopLatch_page`'s, so each of the
four shapes advances the carry; the escape call enters through the caller's two
facts, as in `fusedInv_runFuel`: it answers (`hcall`) and its answer keeps the
document, the staged zeroes, the array's prefix and the stream's prefix
(`hkeep`). -/

/-- **The loop's run, with the carry.**  From the head's invariant, the run at
the escape selection reaches the bound's exit at `for.end101` in at most five
control steps per remaining row plus five, and the terminal carries the loop's
carry. -/
theorem loopRun_carry_aux (sel : Calls) (mem0 : Mem) (xp xn : Nat) (ps : List Nat)
    (bs : List UInt8) (hmodel : PageModel bs) :
    ∀ (r : Nat) (env : Env) (s : State) (c : FusedCarry) (gate escBit : BitVec 1),
      c.shr.toNat - (c.i.toNat + 1) = r →
      c.shr.toNat < 2 ^ 57 →
      c.shr.toNat ≤ blocksOf bs.length →
      blocksOf bs.length < 2 ^ 64 →
      LoopInv mem0 xp xn ps bs env s c gate escBit →
      (∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c) →
      64 * c.shr.toNat ≤ bs.length →
      3 ≤ c.b →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat →
        readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j)) →
      readBytes c.mem (c.b - 3) 3 = some [0, 0, 0] →
      (c.ent + 8 * blocksOf bs.length ≤ xp ∨
        xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) →
      (∀ (args : List Value) (mem : Mem) (next : Nat),
        ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) →
      (∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
          (r : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r →
        (∀ j, j < c'.shr.toNat →
          readBytes r.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
        readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] ∧
        EntryPrefix r.mem c'.ent bs (c'.i.toNat + 1) ∧
        StreamPrefix r.mem xp xn ps) →
      ∃ (e : State) (j : Nat), j ≤ 5 * r + 5 ∧ LoopTerm mem0 xp xn ps bs e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e
  | 0, env, s, c, gate, escBit, hmeasure, hshr57, hshrLe, hblocks64, hinv, hstate,
    hshrBlocks, hb3, hgap, hdoc, hzero, hentXp, hcallAll, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 :=
        toNat_succ_of_lt (by omega)
      have hbound : c.i + 1 = c.shr := by
        apply BitVec.eq_of_toNat_eq
        rw [hsucc]
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
          some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ :=
        readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hcCall⟩ := hcallAll _ _ _
      obtain ⟨hkeepDoc, hkeepZero, hkeepPrefix, hkeepStream⟩ :=
        hkeep c _ _ _ _ _ _ rc hcCall
      obtain ⟨env', core, c', k, hk, hrun, hl, hb', he', hxp', hnxp', hxc', hshr',
        -, -⟩ :=
        loopLatch_page sel env s c gate escBit ((docBlock bs c.i.toNat).take 32)
          ((docBlock bs c.i.toNat).drop 32) mem0 xp xn ps bs hinv.toFusedInv hinv.model
          hmodel hstate hshrBlocks hshr57 hb3 hshrLe hblocks64 hgap hdoc hzero
          hentXp hread73 hread74 rc hcCall hkeepDoc hkeepZero hkeepPrefix hkeepStream
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 1 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).1.mpr hbound
      obtain ⟨hstep, hexit⟩ :=
        fused_latch_exit sel env' core c.i c' gate escBit hl.toFusedLatch hbit
      refine ⟨stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }, k + 1, by omega,
        LoopTerm.exit (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.end101", pre := some "if.end98" }) c' hexit hl.model,
        fun j => ?_⟩
      rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
        runFuel_jump_prefix hstep j]
  | r + 1, env, s, c, gate, escBit, hmeasure, hshr57, hshrLe, hblocks64, hinv, hstate,
    hshrBlocks, hb3, hgap, hdoc, hzero, hentXp, hcallAll, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 :=
        toNat_succ_of_lt (by omega)
      have hne : c.i + 1 ≠ c.shr := by
        intro heq
        have hcongr := congrArg BitVec.toNat heq
        rw [hsucc] at hcongr
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
          some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ :=
        readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hcCall⟩ := hcallAll _ _ _
      obtain ⟨hkeepDoc, hkeepZero, hkeepPrefix, hkeepStream⟩ :=
        hkeep c _ _ _ _ _ _ rc hcCall
      obtain ⟨env', core, c', k, hk, hrun, hl, hb', he', hxp', hnxp', hxc', hshr',
        hdoc', hzero'⟩ :=
        loopLatch_page sel env s c gate escBit ((docBlock bs c.i.toNat).take 32)
          ((docBlock bs c.i.toNat).drop 32) mem0 xp xn ps bs hinv.toFusedInv hinv.model
          hmodel hstate hshrBlocks hshr57 hb3 hshrLe hblocks64 hgap hdoc hzero
          hentXp hread73 hread74 rc hcCall hkeepDoc hkeepZero hkeepPrefix hkeepStream
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 0 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).2.mpr hne
      obtain ⟨hstep, hinv'⟩ :=
        fused_latch_loop sel env' core c.i c' gate escBit hl.toFusedLatch hbit
          (by rw [hshr']; exact hshr57)
      have hmeasure' : c'.shr.toNat - (c'.i.toNat + 1) = r := by
        rw [hshr', hl.succ, hsucc]
        omega
      have hshrLe' : c'.shr.toNat ≤ blocksOf bs.length := by rw [hshr']; exact hshrLe
      have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
        rw [hb', he', hshr']; exact hgap
      have hb3' : 3 ≤ c'.b := by rw [hb']; exact hb3
      have hentXp' : c'.ent + 8 * blocksOf bs.length ≤ xp ∨
          xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c'.ent := by
        rw [he']; exact hentXp
      obtain ⟨e', j, hjle, hterm, hrun'⟩ :=
        loopRun_carry_aux sel mem0 xp xn ps bs hmodel r
          (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.body54", pre := some "if.end98" })
          c' gate escBit hmeasure' (by rw [hshr']; exact hshr57) hshrLe' hblocks64
          { toFusedInv := hinv', model := hl.model } hstate (by rw [hshr']; exact hshrBlocks)
          hb3' hgap'
          (by simpa only [hb', hshr'] using hdoc')
          (by simpa only [hb', hshr'] using hzero')
          hentXp' hcallAll hkeep
      refine ⟨e', (k + 1) + j, by omega, hterm, fun k' => ?_⟩
      rw [show (k + 1) + j + k' = k + (1 + (j + k')) from by omega,
        hrun (1 + (j + k')), runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'

/-- **The loop's run from the head.**  The auxiliary form at the head's own
measure, `%shr - (i + 1)` pages to go. -/
theorem loopRun_carry (sel : Calls) (mem0 : Mem) (xp xn : Nat) (ps : List Nat)
    (bs : List UInt8) (hmodel : PageModel bs) (env : Env) (s : State)
    (c : FusedCarry) (gate escBit : BitVec 1)
    (hstate : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hinv : LoopInv mem0 xp xn ps bs env s c gate escBit)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hcallAll : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r →
      (∀ j, j < c'.shr.toNat →
        readBytes r.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] ∧
      EntryPrefix r.mem c'.ent bs (c'.i.toNat + 1) ∧
      StreamPrefix r.mem xp xn ps) :
    ∃ (e : State) (j : Nat), j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      LoopTerm mem0 xp xn ps bs e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e :=
  loopRun_carry_aux sel mem0 xp xn ps bs hmodel
    (c.shr.toNat - (c.i.toNat + 1)) env s c gate escBit rfl hshr57 hshrLe hblocks64
    hinv hstate hshrBlocks hb3 hgap hdoc hzero hentXp hcallAll hkeep

/-! ### The exit facts, at `FusedExit` -/

/-- **The exit facts.**  The carry at the exit and the run's own frame are
`LoopExitFacts`: the array's prefix and frame, the ASCII and accumulator folds,
and the two lane counts. -/
theorem loopExitFacts_at {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {env : Env} {s : State} {c : FusedCarry}
    (hexit : FusedExit env s c) (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : c.u8k.length = 4) :
    LoopExitFacts mem0 bs c :=
  hc.toLoopExitFacts hframe hu8k haccLen

/-- **The array at the aligned exit.**  At the document's whole block count the
carry's prefix is the post's array, as one read. -/
theorem loopExit_array_full {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hi : c.i.toNat = blocksOf bs.length) :
    readBytes c.mem c.ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) := by
  refine entryWords_of_prefix_full ?_
  show EntryPrefix c.mem c.ent bs (blocksOf bs.length)
  rw [← hi]
  exact hc.arrPrefix

/-- **The peel's slot is the model's word.**  The peel's `%or135` at the model
and the clamp at `%and` make the store read back as `stage1Word`. -/
theorem loopExit_peel_slot {or135 andv w : BitVec 64} {bs : List UInt8}
    {c : FusedCarry}
    (hor : PeelWordAtModel or135 bs c.i.toNat)
    (hlim : limMask andv.toNat = limMask (bs.length - 64 * c.i.toNat))
    (hw : w = or135 &&& limMask andv.toNat) :
    readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
      (c.ent + 8 * c.i.toNat) 8 = some (wordsOf [stage1Word bs c.i.toNat]) := by
  rw [hw]
  exact peel_slot_of_model hor hlim

/-- **The staging at the exit.**  At the exit's block count the carry's two words
are the record's staging. -/
theorem loopExit_staging {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {env : Env} {s : State} {c : FusedCarry}
    (hexit : FusedExit env s c) (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : c.u8k.length = 4)
    {n nb : Nat} {gate : Bool} {err : BitVec 1}
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hi : c.i.toNat = nb)
    (herr : err = 1 ↔ ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs n nb gate err :=
  staging_of_exitFacts (loopExitFacts_at hexit hc hframe hu8k haccLen) hn hnb hi herr

/-- **The tail's two loop facts at the exit.** -/
theorem tail_facts_of_exitCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : c.u8k.length = 4) :
    EntryPrefix c.mem c.ent bs c.i.toNat ∧
      EntryFrame mem0 c.mem c.ent (blocksOf bs.length) :=
  tail_facts_of_exit (hc.toLoopExitFacts hframe hu8k haccLen)

/-- **The peel's three loop facts.**  The prefix at the peel's index, the frame
over the whole array at the peel's store, and the array's one read. -/
theorem tail_peel_facts_of_exitCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {w : BitVec 64}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : c.u8k.length = 4)
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hslot : readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat)
        (natToBytes w.toNat 8)) (c.ent + 8 * c.i.toNat) 8 =
      some (wordsOf [stage1Word bs c.i.toNat])) :
    EntryPrefix c.mem c.ent bs c.i.toNat ∧
      EntryFrame mem0 (writeBytes c.mem (c.ent + 8 * c.i.toNat)
        (natToBytes w.toNat 8)) c.ent (blocksOf bs.length) ∧
      readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
        c.ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) :=
  tail_peel_facts (hc.toLoopExitFacts hframe hu8k haccLen) hsucc hslot

/-- **The tail's aligned shape.**  The loop's memory is the tail's: the entry
array is the model's whole array, the frame is the run's, and the stream's prefix
is the caller's. -/
theorem tail_aligned_of_carry {mem0 : Mem} {xp xn nxp xcarry : Nat}
    {ps : List Nat} {bs : List UInt8} {c : FusedCarry} {arm : BitVec 64}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hi : c.i.toNat = blocksOf bs.length) :
    S1BlocksTail mem0 c.ent xp nxp xcarry xn arm bs c.mem :=
  Or.inl ⟨c.mem, ps, hframe, by
    show EntryPrefix c.mem c.ent bs (blocksOf bs.length)
    rw [← hi]
    exact hc.arrPrefix, hc.stream, rfl⟩

/-- **The tail's peeled shape.**  The peel's store is the run's last write, the
array is the loop's prefix plus the peel's slot, and the frame survives it. -/
theorem tail_peel_of_carry {mem0 : Mem} {xp xn nxp xcarry : Nat}
    {ps : List Nat} {bs : List UInt8} {c : FusedCarry} {arm : BitVec 64}
    {or135 andv w : BitVec 64}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hor : PeelWordAtModel or135 bs c.i.toNat)
    (hshrEq : c.i.toNat = ((BitVec.ofNat 64 bs.length) >>> 6).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 = (0 : BitVec 64)) :
    S1BlocksTail mem0 c.ent xp nxp xcarry xn arm bs
      (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8)) :=
  Or.inr (Or.inl ⟨c.mem, c.i.toNat, or135, andv, w, hframe, hc.arrPrefix, hsucc, hor,
    hshrEq, hand, hw, harm, rfl⟩)

/-- **The terminal's exit facts.**  Every run the induction reaches carries the
loop's facts; the run's own frame is the caller's obligation. -/
theorem loopTerm_exitFacts {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {e : State} (h : LoopTerm mem0 xp xn ps bs e)
    (hframe : ∀ (env : Env) (s : State) (c : FusedCarry), FusedExit env s c →
      LoopCarry mem0 xp xn ps bs c →
      EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : ∀ (env : Env) (s : State) (c : FusedCarry), FusedExit env s c →
      LoopCarry mem0 xp xn ps bs c →
      packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : ∀ (env : Env) (s : State) (c : FusedCarry), FusedExit env s c →
      LoopCarry mem0 xp xn ps bs c → c.u8k.length = 4) :
    ∃ (env : Env) (s : State) (c : FusedCarry),
      FusedExit env s c ∧ LoopExitFacts mem0 bs c := by
  rcases h with ⟨env, s, c, hexit, hc⟩
  exact ⟨env, s, c, hexit,
    hc.toLoopExitFacts (hframe env s c hexit hc) (hu8k env s c hexit hc)
      (haccLen env s c hexit hc)⟩

/-! ### The run at the budget

`s1BlocksInit` is `EntryState` at `next = 1`, so the caller's `next` is the
record's.  The one-prefix's fuel `N` and the exit's run `jE` compose at
`s1BlocksBudget` when `N + jE` is inside it: the prefix's continuation is read at
`budget - N`, and the exit's completed outcome is lifted by fuel monotonicity.
The bound on `N` is the arithmetic the entry's charge names: with the unaligned
exit, the phase's term `3 * (blocks - 1) + 4` and the loop's
`5 * (shr - (i + 1)) + 5` are inside `8 * blocks + 32`
(`s1BlocksBudget_of_entry`), so `s1BlocksBudget_of_phaseCharge` puts any `N`
below that term inside the record's budget. -/

/-- **The caller's `next` is the record's.**  `s1BlocksInit` is `EntryState` at
`next = 1`, definitionally. -/
theorem s1BlocksInit_entryState (args : List Value) (mem : Mem) :
    s1BlocksInit args mem = EntryState s1BlocksFunction args mem 1 := rfl

/-- **The charged one-prefix.**  A run segment from `s1BlocksInit` at some fuel,
ending at the entry's exit terminal.  `JsonS1BlocksStream.s1BlocksPrefix_exit`
produces one, and does not expose its fuel; that number is the whole residual,
so the record's `N` is the caller's to bound. -/
def OnePrefix (esc : Calls) (args : List Value) (mem : Mem) (b : Nat)
    (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64) : Prop :=
  ∃ (e : State) (fuel : Nat),
    (∀ k, runFuel (s1BlocksCallsEsc esc) (fuel + k) s1BlocksFunction
      (s1BlocksInit args mem) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
    ExitTermCells b n conv arm e

/-- **The committed prefix is a `OnePrefix`.**  `s1BlocksPrefix_exit` produces a
segment from `s1BlocksInit` to `for.end101`'s terminal at some fuel; that is a
`OnePrefix` with `fuel` its own `N`.  This is the whole of the residual's first
part: the segment exists, and its fuel is the number the budget must contain. -/
theorem onePrefix_of_exit (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8) (bs73 bs74 : List UInt8)
    (hlong : evalICmp .ult n 64 = 0)
    (hread2 : readBytes mem b 32 = some ((docBlock bs 0).take 32))
    (hread3 : readBytes mem (b + 32) 32 = some ((docBlock bs 0).drop 32))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hfirst : evalICmp .eq (ifEndTest
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w2
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w3) 0 = 0)
    (hgap : b + 64 * (n >>> 6).toNat ≤ ent)
    (hdoc : ∀ j, j < (n >>> 6).toNat →
      readBytes mem (b + 64 * j) 64 = some (doc j))
    (hshr57 : (n >>> 6).toNat < 2 ^ 57)
    (hb3 : 3 ≤ b)
    (hready : ∀ (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
      (v : ForBodyValues),
      AsciiInvCells env s c b n (entryGate arm) arm →
      StreamCells env xp nxp xcarry →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2 →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3 →
      c.i + 1 ≠ c.shr →
      v = asciiValues c bs2 bs3 →
      HandoffCarries esc env s c bs2 bs3 v doc bs73 bs74 xp nxp xcarry) :
    OnePrefix esc [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm] mem b n (entryGate arm) arm :=
  s1BlocksPrefix_exit esc mem b ent xp nxp xcarry n arm bs doc bs73 bs74
    hlong hread2 hread3 hgate hfirst hgap hdoc hshr57 hb3 hready

/-- **The run at `s1BlocksBudget`.**  With the one-prefix's fuel `N` and the
exit's run `jE` inside the budget, the run from `EntryState` at `next = 1`
completes at the budget with the exit's outcome.  The prefix's continuation is
read at `budget - N`, and the exit's completed outcome is lifted to that fuel by
monotonicity. -/
theorem s1BlocksRun_at_budget {esc : Calls} {args : List Value} {mem : Mem}
    {e : State} {N jE : Nat} {ret : BitVec 64} {M : Mem}
    (htrace : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit args mem) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hN : N ≤ s1BlocksBudget args mem)
    (hjE : jE ≤ s1BlocksBudget args mem - N)
    (hexit : runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
      some (.ret (some (.int 64 ret)) M)) :
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
        (EntryState s1BlocksFunction args mem 1) = some (.ret (some (.int 64 ret)) M) := by
  rw [← s1BlocksInit_entryState args mem]
  have hk := htrace (s1BlocksBudget args mem - N)
  rw [show N + (s1BlocksBudget args mem - N) = s1BlocksBudget args mem from by omega] at hk
  rw [hk]
  exact runFuel_mono_le hjE hexit

/-- **The phase's charge inside the record's budget.**  The unaligned exit's
arithmetic (`s1BlocksBudget_of_entry`) with a one-prefix fuel below the phase's
own term: this names exactly what the exposed `fuel` still owes — the bound
itself, not the budget's arithmetic. -/
theorem s1BlocksBudget_of_phaseCharge {args : List Value} {mem : Mem}
    {b ent xp nxp xcarry : Nat} {arm : BitVec 64} {bs : List UInt8}
    {shr i j N : Nat}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm])
    (hn : (BitVec.ofNat 64 bs.length).toNat = bs.length)
    (hshr : shr = ((BitVec.ofNat 64 bs.length) >>> 6).toNat)
    (hi : i + 1 ≤ shr)
    (hmod : (BitVec.ofNat 64 bs.length).toNat % 64 ≠ 0)
    (hj : j ≤ 5 * (shr - (i + 1)) + 5)
    (hN : N ≤ 3 * (blocksOf bs.length - 1) + 4 + j) :
    N ≤ s1BlocksBudget args mem := by
  have h := s1BlocksBudget_of_entry (args := args) (mem := mem) (b := b) (ent := ent)
    (xp := xp) (nxp := nxp) (xcarry := xcarry) (arm := arm) (bs := bs)
    (shr := shr) (i := i) (j := j) hargs hn hshr hi hmod hj
  omega

/-! ### Axiom footprints

The carry steps are `JsonS1BlocksLoopFacts`' page lemmas and the memory store
algebra; the four shapes are `JsonS1BlocksLoop`'s page lemmas; the induction is
on the measure with the caller's two escape facts; the exit facts are
`LoopExitFacts` and `JsonS1BlocksLoopFacts`' tail lemmas; the budget composition
is `runFuel`'s monotonicity and the entry's charge arithmetic.  No statement
reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.LoopCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.LoopCarry.toLoopExitFacts
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.LoopInv
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.LoopLatch
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.LoopTerm
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.LoopTerm.toTerm
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.PageStep
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.PageModel
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.toNat_succ_of_lt
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopCarry_fusedNext
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopCarry_store
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopFrame_store
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopFrame_peel
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopLatch_page
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopRun_carry_aux
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopRun_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopExitFacts_at
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopExit_array_full
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopExit_peel_slot
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopExit_staging
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.tail_facts_of_exitCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.tail_peel_facts_of_exitCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.tail_aligned_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.tail_peel_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.loopTerm_exitFacts
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.s1BlocksInit_entryState
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.OnePrefix
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.onePrefix_of_exit
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.s1BlocksRun_at_budget
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopRun.s1BlocksBudget_of_phaseCharge

end LeanLLVM.Refinement.JsonS1BlocksLoopRun
