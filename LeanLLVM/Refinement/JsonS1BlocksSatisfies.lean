/-
The block unit's record instance.

`Γ_s1_blocks` is the record the pipeline's single call is resolved at
(`JsonS1BlocksContract`), and `s1BlocksPost` is its boundary claim
(`JsonS1BlocksSteps`).  This module proves `s1_blocks_satisfies`: from a staging
the record admits, the run of the pinned unit completes at `s1BlocksBudget` and
every behaviour it has satisfies the record's post.

## What the bundle names

`Satisfies` asks for two things a record read at one body must supply: the run
completes at the record's own budget, and every behaviour satisfies the post.
The post's memory conjuncts are not a fact about the run's existence — they are
the units' lemmas at the arm the tail takes — so the run analysis and the
arm lemmas meet in one bundle, `S1BlocksFacts`, exactly as
`JsonEscapeExpandRun`'s `ExpandFacts` does:

* `run` — the composed run, at `s1BlocksBudget args mem`, returning the verdict
  word and the final memory.  This is `JsonS1BlocksRefines`'s subject: the
  full-run composition from `entry` through the fused loop, `for.end101` and the
  tail.  It is a field, not an assumption about the post.
* `staging` — the loop's carried verdict words as a `VerdictStaging`
  (`JsonS1BlocksEntry.fused_end_staging`).  `post_of_carry` reads the post's
  three bit clauses at it.
* `tail` — the tail's shape, an `S1BlocksTail`: `for.end101`'s aligned exit, or
  the peel's store with the merge's silent arm, or that store and the escape
  call's record.  Each constructor carries the *pre-state* facts the arm's
  memory theorem consumes, and none carries the post's own clauses.

The four loop residuals are named by `S1BlocksTail`'s disjuncts rather than
hidden:

* `EntryPrefix` and the run's frame — the fused loop's per-slot store reading,
  and the frame at the memory the loop hands the tail (`JsonS1BlocksRecordFrame`
  states both; the loop lane's invariant supplies them).  The frame is the
  one-region `EntryFrame` on the two silent shapes and the post's four-region
  list at the escape call's count on the third: a page whose escape bit is set
  calls the list too, so the run's memory is only the caller's outside the
  array, the stream, the count's slot and the carry.
* `StreamPrefix` — the stream's prefix at the caller's count, preserved because
  every escape call stores at or above its cursor.  On the escape arm the
  prefix is moved across the call with `escapeReach_streamPrefix`, from the
  escape record's touched frame and the pre's count/carry separations, so the
  bundle supplies the loop's memory's prefix and this module derives the run's.
* `PeelWordAtModel` — the peel's `%or135` at the model's last block.  The slot's
  store is then the model's word by `limMask_tail_eq` and the two `limMask`s'
  agreement, which is `peel_slot_read`; the peel's own value structure is not
  restated.
* the count room `xn0 + 64 ≤ xn + 64 * blocks` — the loop's accounting at the
  escape call's cursor; with `64` for the block's own positions it makes the
  touched stream extent sit inside the capacity the pre stages.

## What is proved

`S1BlocksTail`'s three shapes are the post's two arms.  The aligned exit
reads the loop's whole entry array (`entryWords_of_prefix_full`), and its count,
stream and carry are the caller's through the loop's frame; its stream prefix is
the staged one, so both of the post's escape branches hold (with the caller's
own count and stream as the witnesses).  The peel's silent arm is
`peel_arm_memory`: the prefix plus the peel's slot, the count and the capacity
read through the peel's store, and the frame widened to the post's four
regions.  The escape arm is `escape_arm_memory`: the same entry array, the
count, the written segment and the carry pair out of the escape record, at
`nxp' = xn0 + position.length`, and the post's frame from the run's four-region
one at `xn0` across the peel's store and the call's segment.

`post_of_carry` reads the returned word's three clauses.  The `arm &&& 2`
hypotheses the post's two branches carry are the tail's own — a peel that took
the merge's silent arm cannot have run the escape list, and one that took the
escape arm cannot have skipped it — so each shape closes the branch it cannot
reach and proves the other.

`s1Blocks_document_of_frame` is the pre's document fact at the *run's* memory:
the post's frame leaves every document block and the three staged zeroes as the
caller staged them, because the pre orders the window against all four regions.
It is what the pipeline's next stage reads.  The per-call form of the same fact
is `s1BlocksPre_escape_keeps_document`, which the loop's induction consumes as
its `hkeep` (and so inside the bundle's `run`); at the whole run's memory the
frame is the post's four regions, and the entry array's separation is the fourth
region `hwinEnt` names.  The post's own document clause is the caller's read at
`mem` and needs no frame.
-/
import LeanLLVM.Refinement.JsonS1BlocksRecordFrame
import LeanLLVM.Refinement.JsonS1BlocksStaging
import LeanLLVM.Refinement.JsonS1BlocksEntry
import LeanLLVM.Refinement.JsonS1BlocksLoop
import LeanLLVM.Refinement.JsonS1BlocksSeparation
import LeanLLVM.Refinement.JsonS1BlocksContract

namespace LeanLLVM.Refinement.JsonS1BlocksSatisfies

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window utf8WinPrefix)
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSeparation

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Two small steps

A memory is unchanged outside any region list relative to itself, which is what
lets the peel's store be read against the loop's own memory instead of the
caller's; and the peel's `limMask` index is the model's, written at the Nat the
store's address uses rather than at the word the block shifts. -/

/-- A memory is unchanged outside anything, relative to itself. -/
theorem frame_refl (m : Mem) (R : List (Nat × Nat)) : UnchangedOutside m m R :=
  fun _ _ => rfl

/-- **The peel's clamp index is the model's, at the peel's Nat slot.**  `%and` is
the document's remainder and `%shr` its whole-block count, so
`bs.length - 64 * shr` is `%and`'s value. -/
theorem limMask_index_eq {bs : List UInt8} {andv : BitVec 64} {shr : Nat}
    (hand : andv.toNat = bs.length % 64) (hshr : shr = bs.length / 64) :
    limMask andv.toNat = limMask (bs.length - 64 * shr) := by
  have hb : bs.length - 64 * shr = andv.toNat := by
    rw [hshr, hand]
    have hdm := Nat.div_add_mod bs.length 64
    omega
  rw [hb]

/-- **The peel's stored word is the model's.**  `PeelWordAtModel` names
`%or135`; the store's word is that word clamped, and the clamp is the model's at
the last block, so the slot reads `stage1Word` back. -/
theorem peel_slot_read {mem : Mem} {ent shr : Nat} {bs : List UInt8}
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

/-! ### The pre at the bundle's witnesses

`s1BlocksPre` is an existential, so a bundle at a particular staging has to state
which witnesses it means.  This is the pre's conjunction at the argument list's
own numbers: the two document reads the post repeats, the four objects'
presence, and the pairwise separations the arm theorems consume. -/

/-- The pre's clauses, at one staging's own witnesses. -/
structure S1BlocksPreAt (mem : Mem) (b ent xp nxp xcarry xn : Nat)
    (arm : BitVec 64) (bs : List UInt8) : Prop where
  /-- The three staged zeroes are addressable. -/
  hb3 : 3 ≤ b
  /-- The document's block count fits the address arithmetic. -/
  hbs63 : bs.length < 2 ^ 63
  /-- The three staged zeroes read as staged. -/
  hzero : readBytes mem (b - 3) 3 = some [0, 0, 0]
  /-- The padded window, as the caller staged it. -/
  hdoc : readBytes mem b (64 * blocksOf bs.length) = some (padded bs)
  /-- The entry array is present. -/
  hentHas : HasBytes mem ent (8 * blocksOf bs.length)
  /-- The count slot holds the caller's count. -/
  hcount : readBytes mem nxp 8 = some (wordBytes 8 xn)
  /-- The count's own bound. -/
  hxn63 : xn < 2 ^ 63
  /-- The stream's capacity is present. -/
  hxpHas : HasBytes mem xp (4 * (xn + 64 * blocksOf bs.length + batchReserve))
  /-- The carry is the all-false pair. -/
  hxcarry : readBytes mem xcarry 16 = some (flagBytes false ++ flagBytes false)
  /-- The block count fits the address arithmetic. -/
  hblkcap : blocksOf bs.length * 64 + 63 < 2 ^ 32
  /-- The window's separation from the entry array. -/
  hwinEnt : b + 64 * blocksOf bs.length ≤ ent ∨
    ent + 8 * blocksOf bs.length ≤ b - 3
  /-- The window's separation from the stream. -/
  hwinXp : b + 64 * blocksOf bs.length ≤ xp ∨
    xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ b - 3
  /-- The window's separation from the count slot. -/
  hwinNxp : b + 64 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ b - 3
  /-- The window's separation from the carry. -/
  hwinXc : b + 64 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ b - 3
  /-- The entry array's separation from the stream. -/
  hentXp : ent + 8 * blocksOf bs.length ≤ xp ∨
    xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ ent
  /-- The entry array's separation from the count slot. -/
  hentNxp : ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent
  /-- The entry array's separation from the carry. -/
  hentXc : ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ ent
  /-- The stream's separation from the count slot. -/
  hxpNxp : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
    nxp + 8 ≤ xp
  /-- The stream's separation from the carry. -/
  hxpXc : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
    xcarry + 16 ≤ xp
  /-- The count slot's separation from the carry. -/
  hnxpXc : nxp + 8 ≤ xcarry ∨ xcarry + 16 ≤ nxp

/-! ### The tail's three shapes

One disjunct per shape the tail's return can take, each naming the pre-state
facts the corresponding arm's memory theorem consumes.  None carries a post
conjunct: the entry array, the escape clauses and the frame are derived below.

`aligned` is `for.end101`'s `%and = 0` exit: the loop wrote every entry word and
nothing else, so the memory is the loop's and the array is `EntryPrefix` at the
document's whole block count.  `peelSilent` is `if.then103` followed by the
merge's `%arm & 2 = 0` arm: the peel's store is the run's last write.
`peelEscape` is the same store followed by the escape list's call, whose record
`EscapeReach` pins the final memory to the call's.  Its frame is the post's four
regions at the count the call was entered with — not the one-region loop frame:
on `arm & 2 ≠ 0` every page of the loop takes the same call, so the run's memory
is the caller's outside the entry array, the stream, the count's slot and the
carry, and the one-region frame is only the silent configuration's.

The bundle carries the caller's count `xn` (the pre's), because that is the
number the post's silent branch reads at the caller's memory and the number the
aligned exit's escape branch reads the staged prefix at.  The escape call's own
cursor is the third disjunct's `xn0`, and the disjunct's array separation is the
extent that call *touched* (`xn0 + position.length`), which the staging's
capacity separation at `xn` and the count's room imply. -/
def S1BlocksTail (mem : Mem) (ent xp nxp xcarry xn : Nat) (arm : BitVec 64)
    (bs : List UInt8) (M : Mem) : Prop :=
  (∃ (memL : Mem) (ps0 : List Nat),
      EntryFrame mem memL ent (blocksOf bs.length) ∧
      EntryPrefix memL ent bs (blocksOf bs.length) ∧
      StreamPrefix memL xp xn ps0 ∧
      M = memL) ∨
  (∃ (memL : Mem) (shr : Nat) (or135 andv w : BitVec 64),
      EntryFrame mem memL ent (blocksOf bs.length) ∧
      EntryPrefix memL ent bs shr ∧
      shr + 1 = blocksOf bs.length ∧
      PeelWordAtModel or135 bs shr ∧
      shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat ∧
      andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64 ∧
      w = or135 &&& limMask andv.toNat ∧
      arm &&& 2 = (0 : BitVec 64) ∧
      M = writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) ∨
  (∃ (memL : Mem) (shr xn0 : Nat) (or135 andv w blk0 : BitVec 64)
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
        xp + 4 * (xn0 + position.length + batchReserve) ≤ ent))

/-! ### The bundle

The run, the staging and the tail's shape at one staging. -/
def S1BlocksFacts (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
    (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8) : Prop :=
  ∃ (ret : BitVec 64) (M : Mem) (ascii u8k : List (BitVec 64)) (err : BitVec 1)
    (gate : Bool) (staging : VerdictStaging ascii u8k bs bs.length
      (blocksOf bs.length) gate err) (hret : ret = verdictWord ascii err),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
      .ptr nxp, .ptr xcarry, .int 64 arm] ∧
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        some (.ret (some (.int 64 ret)) M) ∧
    S1BlocksTail mem ent xp nxp xcarry xn arm bs M

/-! ### The document at the run's memory

`s1BlocksPre_escape_keeps_document` states the pre's document reads survive a
memory that differs from the caller's only inside the escape call's three
regions, at the call's count and position count.  After the whole run the frame
is wider — the post's four regions, the entry array beside the call's three — and
the pre orders the window against all four, so every document byte is outside
each region and reads as the caller staged it.  This is the statement the
pipeline's next stage needs at the arm's own numbers. -/

/-- **The document and the staged zeroes, at the run's memory.**  From the post's
frame and the count room, every document block and the three staged prefix bytes
read as the caller staged them. -/
theorem s1Blocks_document_of_frame {mem M : Mem} {b ent xp nxp xcarry xn xn0 len : Nat}
    {bs : List UInt8}
    (hb3 : 3 ≤ b)
    (hwinEnt : b + 64 * blocksOf bs.length ≤ ent ∨
      ent + 8 * blocksOf bs.length ≤ b - 3)
    (hwinXp : b + 64 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ b - 3)
    (hwinNxp : b + 64 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ b - 3)
    (hwinXc : b + 64 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ b - 3)
    (hframe : UnchangedOutside mem M
      [(ent, 8 * blocksOf bs.length), (xp, 4 * (xn0 + len + batchReserve)),
       (nxp, 8), (xcarry, 16)])
    (hdoc : readBytes mem b (64 * blocksOf bs.length) = some (padded bs))
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hroom : xn0 + len ≤ xn + 64 * blocksOf bs.length) :
    (∀ j, j < blocksOf bs.length → readBytes M (b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes M (b - 3) 3 = some [0, 0, 0] := by
  have hxpT : b + 64 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn0 + len + batchReserve) ≤ b - 3 := by
    rcases hwinXp with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  -- every byte of a document block is outside the post's four regions
  have houtBlock : ∀ k, k < 64 * blocksOf bs.length →
      ∀ r ∈ [(ent, 8 * blocksOf bs.length), (xp, 4 * (xn0 + len + batchReserve)),
        (nxp, 8), (xcarry, 16)], ¬ (r.1 ≤ b + k ∧ b + k < r.1 + r.2) := by
    intro k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hwinEnt with h | h <;> omega
    · rcases hxpT with h | h <;> omega
    · rcases hwinNxp with h | h <;> omega
    · rcases hwinXc with h | h <;> omega
  refine ⟨fun j hj => ?_, ?_⟩
  · have hread := readBytes_of_outside (mem0 := mem) (M := M) (a := b + 64 * j)
      (n := 64) hframe (fun k hk r hr => by
        have hk' : 64 * j + k < 64 * blocksOf bs.length := by omega
        simpa only [Nat.add_assoc] using houtBlock (64 * j + k) hk' r hr)
    rw [hread]
    exact readBytes_docBlock mem bs b hdoc hj
  · have hread := readBytes_of_outside (mem0 := mem) (M := M) (a := b - 3)
      (n := 3) hframe (fun k hk r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rcases hwinEnt with h | h <;> omega
        · rcases hwinXp with h | h <;> omega
        · rcases hwinNxp with h | h <;> omega
        · rcases hwinXc with h | h <;> omega)
    rw [hread]
    exact hzero

/-! ### The post, from the components

Each arm proves the branch the tail can reach.  The aligned exit proves both,
because the caller's own count and staged prefix are the witnesses both branches
read. -/

theorem s1BlocksPost_and_document_of_facts {args : List Value} {mem : Mem} {next : Nat}
    {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    {ret : BitVec 64} {M : Mem} {ascii u8k : List (BitVec 64)} {err : BitVec 1}
    {gate : Bool}
    (hp : S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs)
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
      .ptr nxp, .ptr xcarry, .int 64 arm])
    (hstage : VerdictStaging ascii u8k bs bs.length (blocksOf bs.length) gate err)
    (hret : ret = verdictWord ascii err)
    (htail : S1BlocksTail mem ent xp nxp xcarry xn arm bs M) :
    s1BlocksPost args mem next (.ret (some (.int 64 ret)) M) ∧
      (∀ j, j < blocksOf bs.length → readBytes M (b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes M (b - 3) 3 = some [0, 0, 0] := by
  have hv1 : ret &&& 3 = ret := by
    rw [hret]; exact hstage.satisfies_post.1
  have hv2 : ret &&& 1 = 1 ↔ ∀ x ∈ bs, x.toNat < 0x80 := by
    rw [hret]; exact hstage.satisfies_post.2.1
  have hv3 : ret &&& 2 = 0 ↔
      utf8WinPrefix (utf8Window bs bs.length (blocksOf bs.length)) := by
    rw [hret]; exact hstage.satisfies_post.2.2
  have hnlt : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hp.hbs63; omega)
  rw [hargs]
  simp only [s1BlocksPost]
  rcases htail with ⟨memL, ps0, hframe, hprefix, hstream, hM⟩ | htail
  · -- the aligned exit
    obtain rfl : memL = M := hM.symm
    have hcountM : readBytes memL nxp 8 = some (wordBytes 8 xn) := by
      rw [readBytes_frame_single hframe hp.hentNxp]
      exact hp.hcount
    have hstreamSilent : readBytes memL xp
        (4 * (xn + 64 * blocksOf bs.length + batchReserve)) =
          readBytes mem xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)) :=
      readBytes_frame_single hframe hp.hentXp
    have hcarryM : readBytes memL xcarry 16 =
        some (flagBytes false ++ flagBytes false) := by
      rw [readBytes_frame_single hframe hp.hentXc]
      exact hp.hxcarry
    have hcarryPair : ∃ (st : ClassState) (prevb prevs : Bool),
        carryPair memL xcarry st prevb prevs :=
      ⟨⟨false, false⟩, false, false, hcarryM, rfl⟩
    have hframePost : UnchangedOutside mem memL
        [(ent, 8 * blocksOf bs.length), (xp, 4 * (xn + batchReserve)),
         (nxp, 8), (xcarry, 16)] := by
      refine frame_mono hframe ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact Or.inl hr
    obtain ⟨hdocBlocks, hzeroM⟩ :=
      s1Blocks_document_of_frame (b := b) (ent := ent) (xp := xp) (nxp := nxp)
        (xcarry := xcarry) (xn := xn) (xn0 := xn) (len := 0) hp.hb3 hp.hwinEnt
        hp.hwinXp hp.hwinNxp hp.hwinXc hframePost hp.hdoc hp.hzero (by omega)
    refine ⟨⟨bs, xn, xn, ps0, rfl, hp.hdoc, hp.hcount, hv1, hv2, hv3,
      entryWords_of_prefix_full hprefix, ?_, ?_, hframePost⟩, hdocBlocks, hzeroM⟩
    · intro _
      exact ⟨hcountM, hstreamSilent, hcarryM⟩
    · intro _
      exact ⟨hcountM, hstream, hcarryPair⟩
  · rcases htail with ⟨memL, shr, or135, andv, w, hframe, hprefix, hsucc, hor,
      hshr, hand, hw, hbit, hM⟩ | ⟨memL, shr, xn0, or135, andv, w, blk0, position,
      ps0, opened, ppar, hframe, hprefix, hsucc, hor, hshr, hand, hw, hbit,
      hcountL, hreach, hstream, hlen, hroom, hxpSep⟩
    · -- the peel's silent arm
      subst hM
      have handv : andv.toNat = bs.length % 64 := by
        rw [hand, and_sixtythree_toNat, hnlt]
      have hshrv : shr = bs.length / 64 := by
        rw [hshr, ushr_six_toNat, hnlt]
      have hlim := limMask_index_eq handv hshrv
      have hslot := peel_slot_read (mem := memL) (ent := ent) (shr := shr) hor hlim
      rw [← hw] at hslot
      obtain ⟨staged, hstaged⟩ := hp.hxpHas
      obtain ⟨hentry, hcountM, hstreamM, hcarryM, hframePost⟩ :=
        peel_arm_memory (bs := bs) (ent := ent) (shr := shr) (xn := xn) (xp := xp)
          (nxp := nxp) (xcarry := xcarry) (mem0 := mem) (memL := memL) (w := w)
          (nxp' := xn) (staged := staged) hframe hprefix hsucc hslot hp.hcount
          hstaged hp.hxcarry hp.hentXp hp.hentNxp hp.hentXc
      obtain ⟨hdocBlocks, hzeroM⟩ :=
        s1Blocks_document_of_frame (b := b) (ent := ent) (xp := xp) (nxp := nxp)
          (xcarry := xcarry) (xn := xn) (xn0 := xn) (len := 0) hp.hb3 hp.hwinEnt
          hp.hwinXp hp.hwinNxp hp.hwinXc hframePost hp.hdoc hp.hzero (by omega)
      refine ⟨⟨bs, xn, xn, [], rfl, hp.hdoc, hp.hcount, hv1, hv2, hv3, hentry,
        ?_, ?_, hframePost⟩, hdocBlocks, hzeroM⟩
      · intro _
        refine ⟨hcountM, ?_, hcarryM⟩
        rw [hstreamM, hstaged]
      · intro hne
        exact absurd hbit hne
    · -- the escape arm
      have handv : andv.toNat = bs.length % 64 := by
        rw [hand, and_sixtythree_toNat, hnlt]
      have hshrv : shr = bs.length / 64 := by
        rw [hshr, ushr_six_toNat, hnlt]
      have hlim := limMask_index_eq handv hshrv
      have hslot := peel_slot_read (mem := memL) (ent := ent) (shr := shr) hor hlim
      rw [← hw] at hslot
      have hpeelSelf : EntryFrame memL
          (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) ent
          (blocksOf bs.length) :=
        peelStore_frame (mem0 := memL) (frame_refl memL _) hsucc
          (natToBytes_length w.toNat 8)
      have hsepPeel : ent + 8 * blocksOf bs.length ≤ xp ∨ xp + 4 * xn0 ≤ ent := by
        rcases hxpSep with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have hprefixPeel : readBytes
          (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) xp (4 * xn0) =
            some (positionsBytes 4 ps0) := by
        rw [readBytes_frame_single hpeelSelf hsepPeel]
        exact hstream
      have hkeep : nxp + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ nxp := by
        rcases hp.hxpNxp with h | h
        · exact Or.inr (by unfold blockMax batchReserve at *; omega)
        · exact Or.inl h
      have hcx : xcarry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xcarry := by
        rcases hp.hxpXc with h | h
        · exact Or.inr (by unfold blockMax batchReserve at *; omega)
        · exact Or.inl h
      have hstreamM : StreamPrefix M xp xn0 ps0 :=
        escapeReach_streamPrefix hreach hkeep hcx hprefixPeel
      obtain ⟨hentry, hcountM, hstreamOut, hcarryPair, hframePost⟩ :=
        escape_arm_memory (bs := bs) (ent := ent) (shr := shr) (xn0 := xn0) (xp := xp)
          (nxp := nxp) (xcarry := xcarry) (mem0 := mem) (memL := memL) (M := M)
          (w := w) (position := position) (ps0 := ps0) (opened := opened)
          (ppar := ppar) hframe hprefix hsucc hslot hreach hstreamM hxpSep
          hp.hentNxp hp.hentXc
      obtain ⟨hdocBlocks, hzeroM⟩ :=
        s1Blocks_document_of_frame (b := b) (ent := ent) (xp := xp) (nxp := nxp)
          (xcarry := xcarry) (xn := xn) (xn0 := xn0) (len := position.length)
          hp.hb3 hp.hwinEnt hp.hwinXp hp.hwinNxp hp.hwinXc hframePost hp.hdoc
          hp.hzero (by omega)
      refine ⟨⟨bs, xn, xn0 + position.length,
        ps0 ++ position.map fun k => blockAddr blk0 + k, rfl, hp.hdoc, hp.hcount,
        hv1, hv2, hv3, hentry, ?_, ?_, hframePost⟩, hdocBlocks, hzeroM⟩
      · intro h0
        exact absurd h0 hbit
      · intro _
        exact ⟨hcountM, hstreamOut, hcarryPair⟩

/-! ### The record's instance -/

/-- **The block unit satisfies its record.**  From a staging the record admits,
the run completes at the record's budget and every behaviour satisfies the post.

The bundle is the only hypothesis, and its fields are the run analysis's and the
loop's own residuals, stated at the record's own `pre` witnesses.  Completion is
the bundle's run at `s1BlocksBudget`; the post is
`s1BlocksPost_and_document_of_facts`'s first conjunct at the run's outcome, the
other behaviours being that same outcome by `runFuel_outcome_unique` (so the
`.ub` behaviour `BehFromState` admits is impossible, the post refusing it). -/
theorem s1_blocks_satisfies {esc : Calls}
    (hfacts : ∀ (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs) :
    Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks := by
  intro args mem next hpre
  have hpre0 : s1BlocksPre args mem next := hpre
  have hpreL : s1BlocksPre args mem next := hpre
  unfold s1BlocksPre at hpreL
  obtain ⟨b, ent, xp, nxp, xcarry, arm, bs, xn, hargs, hb3, hzero, hbs63, hdoc,
    hentHas, hcount, hxn63, hxpHas, hxcarryRead, hblkcap, hwinEnt, hwinXp,
    hwinNxp, hwinXc, hentXp, hentNxp, hentXc, hxpNxp, hxpXc, hnxpXc⟩ := hpreL
  have hp : S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs :=
    ⟨hb3, hbs63, hzero, hdoc, hentHas, hcount, hxn63, hxpHas, hxcarryRead,
      hblkcap, hwinEnt, hwinXp, hwinNxp, hwinXc, hentXp, hentNxp, hentXc,
      hxpNxp, hxpXc, hnxpXc⟩
  have hf := hfacts args mem next b ent xp nxp xcarry xn arm bs hpre0 hargs
  obtain ⟨ret, M, ascii, u8k, err, gate, hstage, hret, hargsB, hrun, htail⟩ := hf
  refine ⟨⟨some (.int 64 ret), M, hrun⟩, ?_⟩
  intro o ho
  have hout : o = .ret (some (.int 64 ret)) M := by
    rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact absurd (runFuel_outcome_unique hn hrun) (by intro h; cases h)
    · exact runFuel_outcome_unique hn hrun
  rw [hout]
  exact (s1BlocksPost_and_document_of_facts (next := next) hp hargs hstage hret htail).1

/-! ### The budget's own term

The budget is `8 * blocksOf n + 32`.  `entry_run_charge` reads the entry phase's
and the fused loop's charges at the unaligned exit and finds them inside it, and
`s1BlocksBudget_of_entry` restates that at the record's own budget term, which is
what the run analysis charges against when it composes the bundle's `run`. -/

/-- **The entry's charge at the record's budget.**  With the unaligned exit's
`shr + 1 = blocksOf bs.length`, the phase's `3` per block plus `4` and the
loop's `j ≤ 5 * (shr - (i + 1)) + 5` are inside `s1BlocksBudget`'s
`8 * blocksOf bs.length + 32`. -/
theorem s1BlocksBudget_of_entry {args : List Value} {mem : Mem} {b ent xp nxp xcarry : Nat}
    {arm : BitVec 64} {bs : List UInt8} {shr i j : Nat}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm])
    (hn : (BitVec.ofNat 64 bs.length).toNat = bs.length)
    (hshr : shr = ((BitVec.ofNat 64 bs.length) >>> 6).toNat)
    (hi : i + 1 ≤ shr) (hmod : (BitVec.ofNat 64 bs.length).toNat % 64 ≠ 0)
    (hj : j ≤ 5 * (shr - (i + 1)) + 5) :
    3 * (blocksOf bs.length - 1) + 4 + j ≤ s1BlocksBudget args mem := by
  rw [hargs]
  simp only [s1BlocksBudget, s1BlocksLength]
  rw [hn]
  exact entry_run_charge (BitVec.ofNat 64 bs.length) bs shr i j hn hshr hi hmod hj


/-! ### Footprints

The bundle and the tail's three shapes are definitions; the memory steps read
`Memory`'s store algebra and the two units' frames.  The arm theorems inherit the
peel's value-structure projection (`Classical.choice`, as
`JsonS1BlocksRecordFrame` reports for `escape_arm_memory`/`peel_arm_memory`) and
the verdict staging's carrier, and the record instance adds
`runFuel_outcome_unique` and `Satisfies`'s own definitions. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.frame_refl
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.limMask_index_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.peel_slot_read
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.S1BlocksPreAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.S1BlocksTail
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.S1BlocksFacts
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.s1Blocks_document_of_frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.s1BlocksPost_and_document_of_facts
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.s1_blocks_satisfies
#print axioms LeanLLVM.Refinement.JsonS1BlocksSatisfies.s1BlocksBudget_of_entry

end LeanLLVM.Refinement.JsonS1BlocksSatisfies
