/-
The escape unit's post at the block's call sites, and the loop's exit `ent`.

`JsonS1BlocksRunFrame.loopRun_frame` takes three facts of the caller's escape
selection at every page — the call resolves, the document and the staged zeroes
survive it, and its reach is an `EscapeReach` at the page's count.  It takes them
as hypotheses about arbitrary argument vectors because the page's vector is not
an input of the induction.  The facts themselves are the escape unit's post read
at a call site, and this module derives them there, at the argument vectors the
pages and the peel do use, from the caller's escape entry
(`escapeEntryAt` — the record `Γ_escape_positions` at the selection) and the
staging `s1BlocksPre` admits:

* **`escapeReach_len_of_post`** — the record's post as the shape the loop reads:
  an `EscapeReach` at the caller's block, pointers and count, in the flag-pair
  form `S1BlocksTail`'s calling disjunct names, with the positions a block's
  (at most sixty-four).  The record states the reach's five clauses; this reads
  them back with the length bound `escapePositionsFrom_length_le_block`.
* **`S1BlocksCallReach`** — one call's post: the selection resolves, and what it
  leaves is the record's reach at the count the caller holds, with a block's
  positions at most.  `callReach_of_pre` builds it from `escapeEntryAt` at any
  argument vector the record's `pre` admits, the count identified with the
  record's by the slot's eight bytes (`wordBytes_eq_of_lt`).
* **`keep_of_call`** — the document and the staged zeroes at the call's memory.
  The record's frame from the call's entering memory to its outcome is widened to
  the block's spelling (`escapeReach_callRegions`), composed with the run's frame
  to that entering memory, and read through the staging's separations
  (`keep_of_frame`, `s1BlocksPre_escape_keeps_document`'s statement).  The
  count's room is the caller's: the run's frame is at the count the call was
  entered with, and the record's positions are a block's.
* **`peel_keep`** — the same at the peel's call, whose entering memory is the
  loop's plus the peel's store inside the entry array
  (`frame_write_in_region`).
* **`S1BlocksUnitPostAt`** — the three facts at one call, bundled: the two
  readings above (`callReach_of_pre`, `keep_of_call`) give it, at the pages'
  vector (`unitPostAt_of_pre`) and at the peel's (`peel_unitPostAt_of_pre`).

The second half is the loop's exit `ent`.  The pages never write `%ent`, so the
carry's `ent` is the head's at `for.end101` — `loopPage_zero` states it for one
page, but `loopRun_frame_aux`'s exit bundle does not carry it, and the residual's
tail is stated at the caller's `ent` while `tail_third_of_frame` names the exit
carry's.  `loopRun_frame_ent_aux` and `loopRun_frame_ent` are that induction with
the one conjunct added: the exit carry's `ent` is the head's.  `tail_third_at_ent`
reads the residual's tail at the caller's `ent` from the peel's own reach, and
`tail_calling_at_ent` the same from `JsonS1BlocksFinal.S1BlocksUnitPost`'s bundle.

## The unit post at a call, and the bundle in `JsonS1BlocksFinal`

`S1BlocksUnitPost` quantifies over argument vectors the escape record's `pre` does
not admit — the loop's induction cannot know the page's vector when it takes the
hypothesis — and its document clause is not a function of the call's arguments at
all: the vector is the three mask words, the block's index and the three
pointers, so neither the window's base `b` nor the bound `%shr` is available to
the callee, and a selection that only reads its arguments cannot place a
document block.  The structure is therefore a promise about a selection that
keeps a window it is never told about; the record establishes its post at the
vectors `Γ_escape_positions.pre` admits, which are the pages' and the peel's, and
`S1BlocksUnitPostAt` is that statement — `unitPostAt_of_pre` /
`peel_unitPostAt_of_pre` are it from `escapeEntryAt` and the staging.  What
discharges the loop is the record at the vectors the run actually uses; the
committed bundle stays what it was, a named hypothesis at the induction.

## What remains

The unit-post facts are stated at a call site: the record's `pre` at the page's
or the peel's argument vector is the hypothesis, exactly as
`JsonS1BlocksRefine.escapeEntryAt` and `JsonS1BlocksCompose`'s call steps take it.
Deriving that `pre` from the block's own staging — the page's three mask words as
the block's classifier words (`JsonS1BlocksLoopRun.PageCarry`) and the carry pair
— is the loop's lane, and nothing here states it.  The accumulator's fold at the
exit is `JsonS1BlocksPageModel.exit_staging_of_*`'s input and is not touched here
either.
-/
import LeanLLVM.Refinement.JsonS1BlocksFinal
import LeanLLVM.Refinement.JsonS1BlocksSeparation

namespace LeanLLVM.Refinement.JsonS1BlocksUnitPost

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksRunFrame
open LeanLLVM.Refinement.JsonS1BlocksFinal

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The record's post, as the loop reads it

`escapeReach_flag_of_post` reads the record's post as an `EscapeReach` in the
flag-pair form; the loop also needs the positions' bound and, at the page's own
count, the slot's read.  All three come out of the same destructuring. -/

/-- **The record's post at the caller's block, pointers and count.**  The post's
count, segment, carry and presence clauses are the reach's; the frame is its
last.  The positions are a block's, so there are at most sixty-four, and the
count the post read in is the slot's word below `2 ^ 64`. -/
theorem escapeReach_len_of_post {base : Nat} {bs ctl im blk0 : BitVec 64}
    {xp xn carry : Nat} {mem M : Mem}
    (h : escapePositionsPost base
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
        .ptr carry] mem M) :
    ∃ (xn0 : Nat) (position : List Nat) (opened ppar : Bool),
      EscapeReach blk0 xp xn carry xn0 position
        (flagBytes opened ++ flagBytes ppar) mem M ∧
      position.length ≤ 64 ∧
      readBytes mem xn 8 = some (wordBytes 8 xn0) ∧
      xn0 < 2 ^ 64 := by
  obtain ⟨xp', xn', carry', blk0', bs', ctl', im', lo, hi, st, prevb, prevs, xn0,
    hargs, _hblock, _hbs, _hctl, _him, _hpairIn, hcntIn, hxn0, hcntOut, hposOut,
    hpairOut, hhasOut, hframeOut⟩ := h
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨_hbsE, _hctlE, _himE, hblkE, hxpE, hxnE, hcarryE⟩ := hargs
  subst hxpE; subst hxnE; subst hcarryE
  have hblkEq : blk0' = blk0 := (eq_of_heq hblkE).symm
  subst hblkEq
  refine ⟨xn0, escapePositionsFrom (block64 lo hi) st,
    IsBackslashB (hi ⟨31, by decide⟩), (carry64 lo hi st).oddRun,
    ⟨?_, ?_, hpairOut.1, hhasOut, ?_⟩,
    escapePositionsFrom_length_le_block lo hi st, hcntIn, hxn0⟩
  · simpa using hcntOut
  · simpa [blockPositions] using hposOut
  · simpa using hframeOut

/-! ### The staging's own witnesses

`s1BlocksPre` is an existential, so a frame stated at the caller's own numbers
has to name the witnesses it is read against.  These are the pre's clauses as
`JsonS1BlocksSatisfies.S1BlocksPreAt`, which is the structure the post's arm
theorems already consume. -/

/-- **The staging's clauses, from the pre.** -/
theorem preAt_of_pre {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s1BlocksPre args mem next) :
    ∃ (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs := by
  unfold s1BlocksPre at hpre
  obtain ⟨b, ent, xp, nxp, xcarry, arm, bs, xn, _hargs, hb3, hzero, hbs63, hdoc,
    hentHas, hcount, hxn63, hxpHas, hxcarryRead, hblkcap, hwinEnt, hwinXp,
    hwinNxp, hwinXc, hentXp, hentNxp, hentXc, hxpNxp, hxpXc, hnxpXc⟩ := hpre
  exact ⟨b, ent, xp, nxp, xcarry, xn, arm, bs,
    ⟨hb3, hbs63, hzero, hdoc, hentHas, hcount, hxn63, hxpHas, hxcarryRead,
      hblkcap, hwinEnt, hwinXp, hwinNxp, hwinXc, hentXp, hentNxp, hentXc,
      hxpNxp, hxpXc, hnxpXc⟩⟩

/-! ### The count the chain reaches

The pages' count is the caller's plus at most a block's worth per page, and the
staging bounds the caller's count and the block count, so it is still a value a
slot's eight bytes decide.  This is the `hcountLt` the call's post takes. -/

/-- **The pages' count is below `2 ^ 64`.**  The staging's count bound
(`xn < 2 ^ 63`) and block cap (`blocks * 64 + 63 < 2 ^ 32`) put the count the
chain reaches — the caller's plus a block's worth per page — inside a word. -/
theorem count_lt_two_pow {mem : Mem} {b ent xp nxp xcarry xn : Nat}
    {arm : BitVec 64} {bs : List UInt8}
    (hp : S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs)
    {count : Nat} (hcount : count ≤ xn + 64 * blocksOf bs.length) :
    count < 2 ^ 64 := by
  have h1 := hp.hxn63
  have h2 := hp.hblkcap
  omega

/-! ### The document and the staged zeroes at a call

The escape record's frame is at the stream's cursor; the block's spelling is the
stream's base, widened once by `escapeReach_callRegions`.  The staging's
separations then order every document block and the three staged bytes away from
all four regions, so they read as the caller staged them:
`s1BlocksPre_escape_keeps_document`'s statement at the composed frame. -/

/-- **The document and the staged zeroes at a memory the four regions reach.**
The staging orders the window against the entry array and the call's three
regions, so a memory that differs from the caller's only inside them reads the
window and the prefix back.  This is `s1Blocks_document_of_frame` at the block's
four-region list, which is `escapeCallWriteRegions` at the count the frame names
and no further positions. -/
theorem keep_of_frame {mem M : Mem} {b ent xp nxp xcarry xn xnB : Nat}
    {arm : BitVec 64} {bs : List UInt8}
    (hp : S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs)
    (hframe : UnchangedOutside mem M
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnB))
    (hroom : xnB ≤ xn + 64 * blocksOf bs.length) :
    (∀ j, j < blocksOf bs.length →
      readBytes M (b + 64 * j) 64 = some (docBlock bs j)) ∧
    readBytes M (b - 3) 3 = some [0, 0, 0] := by
  have hframe' : UnchangedOutside mem M
      [(ent, 8 * blocksOf bs.length), (xp, 4 * (xnB + 0 + batchReserve)),
       (nxp, 8), (xcarry, 16)] := by
    rw [← escapeCallWriteRegions_eq_post]
    exact hframe
  exact s1Blocks_document_of_frame (b := b) (ent := ent) (xp := xp) (nxp := nxp)
    (xcarry := xcarry) (xn := xn) (xn0 := xnB) (len := 0) hp.hb3 hp.hwinEnt
    hp.hwinXp hp.hwinNxp hp.hwinXc hframe' hp.hdoc hp.hzero (by omega)

/-- **One call's document and staged zeroes.**  The frame from the caller's
memory to the call's entering memory — the pages' chain, the peel's store, or
neither — is widened to the count the call leaves, the call's own three regions
are its tail, and `keep_of_frame` reads the window through the composition.  The
count's room is the caller's, and the record's positions are a block's. -/
theorem keep_of_call {mem0 memL : Mem} {b ent xp nxp xcarry xn count : Nat}
    {bs : List UInt8} {arm : BitVec 64} {blk0 : BitVec 64}
    {out : CallOutcome} {position : List Nat} {opened ppar : Bool}
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    (hreach : EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar) memL out.mem)
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry count))
    (hroom : count + position.length ≤ xn + 64 * blocksOf bs.length) :
    (∀ j, j < blocksOf bs.length →
      readBytes out.mem (b + 64 * j) 64 = some (docBlock bs j)) ∧
    readBytes out.mem (b - 3) 3 = some [0, 0, 0] := by
  have hwide := escapeCallWriteRegions_widen hframe
    (show count ≤ count + position.length from Nat.le_add_right _ _)
  have hcomp := frame_comp hwide (escapeReach_callRegions hreach)
    (fun r hr => List.mem_cons_of_mem _ hr)
  exact keep_of_frame hp hcomp (by omega)

/-- **The count's slot at the peel's stored memory.**  The peel's store is inside
the entry array, so the slot reads as the pages left it.  This is the count
`peel_unitPostAt_of_pre` takes at the peel's entering memory, from the pages'
own read and the staging's separation of the array from the slot. -/
theorem peel_count_read {memL : Mem} {ent shr blocks nxp xnA : Nat}
    {word : List UInt8}
    (hsep : ent + 8 * blocks ≤ nxp ∨ nxp + 8 ≤ ent)
    (hsucc : shr + 1 = blocks)
    (hwlen : word.length = 8)
    (hcount : readBytes memL nxp 8 = some (wordBytes 8 xnA)) :
    readBytes (writeBytes memL (ent + 8 * shr) word) nxp 8 =
      some (wordBytes 8 xnA) := by
  rw [readBytes_writeBytes_frame memL word (ent + 8 * shr) nxp 8 ?_]
  · exact hcount
  · rcases hsep with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- **The peel's document and staged zeroes at its call.**  The peel's store is
inside the entry array, so the caller's frame to the pages' memory is a frame to
the stored one; `keep_of_call` then composes it with the call's three regions. -/
theorem peel_keep {mem0 memL : Mem} {b ent shr xn xp nxp xcarry xnA : Nat}
    {bs : List UInt8} {arm : BitVec 64} {blk0 : BitVec 64} {word : List UInt8}
    {out : CallOutcome} {position : List Nat} {opened ppar : Bool}
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    (hreach : EscapeReach blk0 xp nxp xcarry xnA position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes memL (ent + 8 * shr) word) out.mem)
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA))
    (hsucc : shr + 1 = blocksOf bs.length)
    (hwlen : word.length = 8)
    (hroom : xnA + position.length ≤ xn + 64 * blocksOf bs.length) :
    (∀ j, j < blocksOf bs.length →
      readBytes out.mem (b + 64 * j) 64 = some (docBlock bs j)) ∧
    readBytes out.mem (b - 3) 3 = some [0, 0, 0] := by
  have hstore : UnchangedOutside mem0 (writeBytes memL (ent + 8 * shr) word)
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA) :=
    frame_write_in_region hframe (by omega) (by omega)
  exact keep_of_call hp hreach hstore hroom

/-! ### One call's post, from the caller's escape entry

The record read at the caller's escape entry, at the argument vector the pages
and the peel use: three mask words, the block's index, and the stream, count and
carry pointers.  The count is the caller's own — the slot's eight bytes decide it
between two representatives below `2 ^ 64` — which is the number the loop's chain
carries, so the reach is stated at it rather than at the record's witness. -/

/-- **The escape call's reach at one call site.**  The selection resolves the
call, and what it leaves is the record's reach at the caller's count, with a
block's positions at most. -/
def S1BlocksCallReach (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
    (blk0 : BitVec 64) (xp nxp xcarry count : Nat) : Prop :=
  ∃ (out : CallOutcome) (position : List Nat) (opened ppar : Bool),
    esc escapeListCallee args mem next = some out ∧
    EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar) mem out.mem ∧
    position.length ≤ 64

/-- **The call's reach, from the caller's escape entry.**  The record's own `pre`
at the argument vector in, the post's reach at the caller's count out. -/
theorem callReach_of_pre {esc : Calls} {base : Nat} (hEsc : escapeEntryAt esc base)
    {or14 mask xs i : BitVec 64} {xp nxp xcarry count : Nat} {mem : Mem} {next : Nat}
    (hpre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] mem next)
    (hcount : readBytes mem nxp 8 = some (wordBytes 8 count))
    (hcountLt : count < 2 ^ 64) :
    S1BlocksCallReach esc
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] mem next i xp nxp xcarry count := by
  obtain ⟨r, hcall, hpost, _hnext⟩ := escapeEntry_call hEsc hpre
  obtain ⟨xn0, position, opened, ppar, hreach, hlen, hcntIn, hxn0⟩ :=
    escapeReach_len_of_post hpost
  have hcount' : xn0 = count := wordBytes_eq_of_lt hxn0 hcountLt
    (Option.some.inj (hcntIn.symm.trans hcount))
  rw [hcount'] at hreach
  exact ⟨r, position, opened, ppar, hcall, hreach, hlen⟩

/-- **The unit's post at one call site.**  The selection resolves the call, its
reach is the record's at the caller's count, and the document and the staged
zeroes survive it — the three facts the loop's induction reads, at one vector. -/
def S1BlocksUnitPostAt (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
    (blk0 : BitVec 64) (xp nxp xcarry count : Nat)
    (mem0 : Mem) (b ent xn : Nat) (arm : BitVec 64) (bs : List UInt8) : Prop :=
  ∃ (out : CallOutcome) (position : List Nat) (opened ppar : Bool),
    esc escapeListCallee args mem next = some out ∧
    EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar) mem out.mem ∧
    position.length ≤ 64 ∧
    (∀ j, j < blocksOf bs.length →
      readBytes out.mem (b + 64 * j) 64 = some (docBlock bs j)) ∧
    readBytes out.mem (b - 3) 3 = some [0, 0, 0]

/-- **The unit's post at one page's call.**  `callReach_of_pre`'s reach and
`keep_of_call`'s document, at the vector the page's arm calls with; the room is
the loop's own (`count + 64 ≤ xn + 64 * blocks`). -/
theorem unitPostAt_of_pre {esc : Calls} {base : Nat} (hEsc : escapeEntryAt esc base)
    {or14 mask xs i : BitVec 64} {xp nxp xcarry count : Nat} {mem : Mem} {next : Nat}
    {mem0 : Mem} {b ent xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    (hpre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] mem next)
    (hcount : readBytes mem nxp 8 = some (wordBytes 8 count))
    (hcountLt : count < 2 ^ 64)
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    (hframe : UnchangedOutside mem0 mem
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry count))
    (hroom : count + 64 ≤ xn + 64 * blocksOf bs.length) :
    S1BlocksUnitPostAt esc
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] mem next i xp nxp xcarry count
      mem0 b ent xn arm bs := by
  obtain ⟨out, position, opened, ppar, hcall, hreach, hlen⟩ :=
    callReach_of_pre hEsc hpre hcount hcountLt
  obtain ⟨hdoc, hzero⟩ := keep_of_call hp hreach hframe (by omega)
  exact ⟨out, position, opened, ppar, hcall, hreach, hlen, hdoc, hzero⟩

/-- **The unit's post at the peel's call.**  The same at the peel's vector and
the peel's entering memory, the loop's frame folded across the peel's store. -/
theorem peel_unitPostAt_of_pre {esc : Calls} {base : Nat}
    (hEsc : escapeEntryAt esc base)
    {or14 mask xs i : BitVec 64} {xp nxp xcarry xnA : Nat} {next : Nat}
    {mem0 memL : Mem} {b ent shr xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    {word : List UInt8}
    (hpre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] (writeBytes memL (ent + 8 * shr) word) next)
    (hcount : readBytes (writeBytes memL (ent + 8 * shr) word) nxp 8 =
      some (wordBytes 8 xnA))
    (hcountLt : xnA < 2 ^ 64)
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xnA))
    (hsucc : shr + 1 = blocksOf bs.length)
    (hwlen : word.length = 8)
    (hroom : xnA + 64 ≤ xn + 64 * blocksOf bs.length) :
    S1BlocksUnitPostAt esc
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] (writeBytes memL (ent + 8 * shr) word)
      next i xp nxp xcarry xnA mem0 b ent xn arm bs := by
  obtain ⟨out, position, opened, ppar, hcall, hreach, hlen⟩ :=
    callReach_of_pre hEsc hpre hcount hcountLt
  obtain ⟨hdoc, hzero⟩ := peel_keep hp hreach hframe hsucc hwlen (by omega)
  exact ⟨out, position, opened, ppar, hcall, hreach, hlen, hdoc, hzero⟩

/-! ### The loop's exit carries the caller's `ent`

The pages' stores are inside the entry array and their calls name only the
stream, the count's slot and the carry, so `%ent` is the head's at every page;
`loopPage_zero` states `c'.ent = c.ent` for the page it analyses, and the
induction below carries it.  `JsonS1BlocksRunFrame.loopRun_frame_aux`'s exit
bundle states the model's carry, the chain and the peel's index, but not `ent`,
which is why the induction is restated here rather than read off it. -/

/-- **The loop's calling run, with the carry's `ent`.**  `loopRun_frame_aux`'s
rows and hypotheses, with one conjunct added to the exit: the carry's `ent` at
`for.end101` is the head's. -/
theorem loopRun_frame_ent_aux (sel : Calls) (start : Mem) (xp xn nxp xcarry : Nat)
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
        c'.ent = c.ent ∧
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
        by omega, hsuccBlocks, he', fun j => ?_⟩
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
        hpages'', hsucc'', hent'', hrun'⟩ :=
        loopRun_frame_ent_aux sel start xp xn nxp xcarry bs hstoreAll r
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
        hfr'', hpages'', hsucc'', hent''.trans he', fun k' => ?_⟩
      rw [show k + 1 + j + k' = k + (1 + (j + k')) from by omega,
        hrun (1 + (j + k')), runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'

/-- **The loop's calling run from the head, at the caller's `ent`.**  The
auxiliary form at the head's own measure, `%shr - (%i + 1)` rows to go, with the
caller's staging as the chain's first node; the exit's carry is at the head's
`ent`, and the head's is the caller's. -/
theorem loopRun_frame_ent (sel : Calls) (start : Mem) (xp xn nxp xcarry : Nat)
    (bs : List UInt8)
    (hstoreAll : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < blocksOf bs.length →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat)
    (env : Env) (s : State)
    (c : FusedCarry) (gate : BitVec 1) (ps : List Nat) (ent : Nat)
    (hent : c.ent = ent)
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
      c'.ent = ent ∧
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
  obtain ⟨env', e, c', count, pages, j, hj, hexit, hcarry, hfr, hpages, hsucc,
    hent', hrun⟩ :=
    loopRun_frame_ent_aux sel start xp xn nxp xcarry bs hstoreAll
      (c.shr.toNat - (c.i.toNat + 1)) env s c gate xn 0 ps rfl hpages0 hblocks
      hshr57 hshrLe hblocks64 hinv hframe0 hb3 hgap hdoc hzero hentXp hentNxp
      hentXc hxpNxp hxpXc hcallAll hkeep hreachAll
  exact ⟨env', e, c', count, pages, j, hj, hexit,
    { carry := hcarry, frame := hfr, succ := hsucc, pagesLe := hpages },
    hent'.trans hent, hrun⟩

/-- **The residual's tail at the caller's `ent`, from the peel's own reach.**
`tail_third_of_frame` at the exit, its `EscapeReach` read off the escape record at
the peel's call (`S1BlocksCallReach`) and the exit carry's `ent` identified with
the caller's.  This is the composition the residual's `tail` field takes: the
record's reach at the peel, not a hypothesis about the selection at every
argument vector. -/
theorem tail_third_at_ent {start : Mem} {xp xn nxp xcarry : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {count pages : Nat} {arm : BitVec 64}
    {M : Mem} {shr ent : Nat} {or135 andv w blk0 : BitVec 64}
    {position : List Nat} {opened ppar : Bool}
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hent : c.ent = ent)
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
    S1BlocksTail start ent xp nxp xcarry xn arm bs M := by
  rw [← hent]
  exact tail_third_of_frame hrun hshr hor hshrEq hand hw harm hreach hlen hxpSep

/-- **The residual's tail at the caller's `ent`, from the unit's bundled post.**
`tail_calling_of_unitPost` concludes at the exit carry's `ent`; the loop's
induction above supplies that the exit carry's is the caller's, which is the
number the residual's tail field is stated at. -/
theorem tail_calling_at_ent {esc : Calls} {start : Mem}
    {xp xn nxp xcarry : Nat} {ps : List Nat} {bs : List UInt8} {c : FusedCarry}
    {count pages : Nat} {arm : BitVec 64} {M : Mem} {shr : Nat} {ent : Nat}
    {or135 andv w : BitVec 64} {or14 mask xs i : BitVec 64} {next : Nat}
    {r' : CallOutcome}
    (hu : S1BlocksUnitPost esc xp nxp xcarry bs)
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hent : c.ent = ent)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hcall : esc escapeListCallee
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) next = some r')
    (hrM : r'.mem = M)
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    S1BlocksTail start ent xp nxp xcarry xn arm bs M := by
  rw [← hent]
  exact tail_calling_of_unitPost hu hrun hshr hor hshrEq hand hw harm hcall hrM hxpSep

/-! ### Axiom footprints

The record's post is `escapePositionsPost`'s destructuring and the length bound
is `escapePositionsFrom_length_le_block`'s; the call's post adds
`wordBytes_eq_of_lt`.  The document facts are the pre's clauses read through
`frame_comp` and `escapeReach_callRegions` into
`JsonS1BlocksSatisfies.s1Blocks_document_of_frame`, which is
`JsonS1BlocksSeparation.s1BlocksPre_escape_keeps_document`'s statement at the
four-region list; the peel's add `frame_write_in_region`.  The induction is
`loopPage_zero`, `fused_latch_exit`, `fused_latch_loop` and the chain's steps, as
`loopRun_frame_aux`'s own; the two tail statements are `tail_third_of_frame`'s
and `tail_calling_of_unitPost`'s.  `Classical.choice` accompanies the store
arithmetic `omega` discharges.  No statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.escapeReach_len_of_post
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.preAt_of_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.count_lt_two_pow
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.keep_of_frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.keep_of_call
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.peel_count_read
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.peel_keep
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.S1BlocksCallReach
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.callReach_of_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.S1BlocksUnitPostAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.unitPostAt_of_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.peel_unitPostAt_of_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.loopRun_frame_ent_aux
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.loopRun_frame_ent
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.tail_third_at_ent
#print axioms LeanLLVM.Refinement.JsonS1BlocksUnitPost.tail_calling_at_ent

end LeanLLVM.Refinement.JsonS1BlocksUnitPost
