/-
The two-entry token: the standalone string's bundle and its `merge` arm.

## What this bundle is

`HstringFacts` is the input's facts at a head state whose token consumes **two**
entries — a standalone string's opener and its closer — grouped by subject, and
`WalkDispatchResult.ofStringMerge` is the `merge` arm those facts support: the
dispatch reaches `cleanup478.i` with `%k.2.i = %inc208.i = %k.0.i249 + 2` and
`%nep`, so at `C.k = 0`, `G.nep = 2` the outcome is a `finish` and the loop does
not run again.  That is the case `standaloneString_finish`
(`JsonStage2WalkDispatchThreeOfRun`) states and the case the head's own test
(`C.k + 1 < G.nep`, which is `0 + 1 < 2`) cannot classify: the continuing
bundle `HcontFacts` describes a *one*-entry token and is uninhabited here, so
without this bundle the continuing branch of `walkLoopStep_of_staging` is
vacuous at exactly the input the dispatch handles.

The bundle is a `Type` for the reason `HlastFacts` and `HcontFacts` are: its
first field of each group is a witness (`x`, `ep`/`bs`/`q`, `root`/`rd`/`xv`,
`ix`/`ext`/`A`, `Cc`, `y`) that the rest of the group is stated at, and a
`Prop`-valued structure cannot carry data.

### The fifteen-block path

The arm walks, from the dispatch's head `NodeBlock21`:

| # | block | link |
|---|---|---|
| 1 | `NodeBlock21` | `WalkLink.NodeBlock21_at` |
| 2 | `NodeBlock5` | `WalkLink.NodeBlock5_at` |
| 3 | `LeafBlock` | `WalkLink.LeafBlock_at` |
| 4 | `sw.bb202.i` | `WalkLink.sw_bb202_i_at` |
| 5 | `if.end207.i` | `WalkLink.if_end207_i` |
| 6 | `if.then219.i` | `WalkLink.if_then219_i` |
| 7 | `if.end245.i` | `WalkLink.if_end245_i` |
| 8 | `if.end256.i` | `WalkLink.if_end256_i` |
| 9 | `z_arena_reserve.exit` | `WalkLink.z_arena_reserve_exit` |
| 10 | `NodeBlock31` | `WalkLink.NodeBlock31_at` |
| 11 | `LeafBlock29` | `WalkLink.LeafBlock29_at` |
| 12 | `if.then281.i` or `if.else285.i` | `WalkLink.if_then281_i` / `WalkLink.if_else285_i_at` |
| 13 | `if.end290.i` | `WalkLink.if_end290_i` |
| 14 | `if.then328.i` | `WalkLink.if_then328_i` |
| 15 | `if.else334.i` | `WalkLink.if_else334_i` |

so fifteen control steps to `cleanup478.i`, the count the merge arm's price is
stated at (`15 + 2`).  Two arm choices are fixed and the bundle is stated for
them: the **depth-zero** arm (`C.sp = 0`, group G4), which is why the path goes
`if.then219.i → if.end245.i` and not through `land.lhs.true.i`/`if.then231.i`
— the depth-positive arm is a second branch the same block reaches — and the
**key-zero** arm, which is what the depth-zero entry carries into
`if.end245.i`'s `%key.1.i` phi (its `if.then219.i` incoming operand is
`imm 0`), so `if.then328.i` takes `if.else334.i` and not `if.then330.i`.
Position 12 is either `if.then281.i` (the callee's literal form `1`) or
`if.else285.i` (the write-back); both are one link, so both arms count 15.

### The segment is supplied, not composed

**The arm itself is produced.**  `WalkDispatchResult.ofStringMerge` is a theorem
from the bundle — the `merge` arm, its index, its depth, its two bounds and its
price are all read from fields and from the invariant at the segment's endpoint.
What is supplied is the **segment** inside the bundle, not the case, not the arm
and not its classification: `WalkDispatchResult.toOutcome` still decides
`cont`/`finish` from the merge's own test on the index the segment reached.

**The intermediate states are now nameable.**  A composition threads each link's
*target* state into the next link's hypotheses, and until recently five of the
fifteen links concluded `∃ s', WalkLink … s'` without saying which state `s'` is,
so no `def` could name them and no bundle field could be stated at them.  Those
conclusions now carry the equality: `WalkLink.if_then281_i`
(`JsonStage2WalkRest`), `WalkLink.if_end207_i` (`JsonStage2WalkStore`),
`WalkLink.if_end245_i` and `WalkLink.if_end290_i` (`JsonStage2WalkPhi`), and
`WalkLink.if_then219_i` (`JsonStage2WalkCall`) each conclude
`∃ s', WalkLink … s' ∧ s' = <the state the run reaches>`, the shape seven of the
fifteen links already had (`NodeBlock21_at`, `NodeBlock5_at`, `LeafBlock_at`,
`sw_bb202_i_at`, `NodeBlock31_at`, `LeafBlock29_at`, `if_else285_i_at`).  Of the
three that did not, `if_end256_i` and `z_arena_reserve_exit` now name their
targets (`walkIfEnd256OutAt`, `walkZArenaReserveExitOutAt`, the second taking the
callee's `CallOutcome` as a parameter), and only `if_then328_i` remains to be
exposed for the write-back links.

**The residue: four fields, not eight links.**  With the states nameable, every
link's hypotheses are the head bundle's fields, `WalkInv`'s clauses, the step's own
predecessor, or a `def`'d state's cells — except for four facts, each of which is
named here with the producer that will retire it:

* **`z_arena_reserve_exit`'s witness** — one premise, not six fields:
  `UnchangedOutside r.mem (walkWide G C₉) ∧ howned ∧ hlog ∧ hev ∧ hstTy ∧ hstSt`
  at the state link 8 leaves, with the callee's `r` and its answer's word beside
  it.  It is `strPath10`'s `hbodyR`; producer: `s2StringBodyFoot_frame_walkWide`
  (`JsonStage2StringStageFacts`) plus the four `walkReadBytes_*` crossings that
  `walkAfterValue_facts` already carries for `s2_after_value`.  Retired by the
  cursor-parameterised frame.
* **`l ≤ ext`** at `if.else285.i`'s state — the decoded length fits the window
  `if.end256.i` reserved.  Producer: `s2StringBody_outn_le`.
* **the log's base word**, `readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)`.
  Not a lemma: `%z`'s first eight bytes are *inside* the walk's write extent, so
  `WalkInv.frame` (silence outside it) cannot reach them and the staging gives
  presence, not the value.  Producer: the initialisation's store at `%z + 0` — a
  `WalkSeedState` fact the record does not yet carry — **plus** a `WalkInv` clause
  for the log's base word, because the seed alone does not give the fact at the
  state that reads it.  The retirement is that clause.
* **`C.events.length < C.k`** (strict; `events_le` gives `≤`).  Producer:
  `if.then425.i`'s one-record-per-emitting-entry count.

`hinc208`/`hnepM` stay as fields of a `∀` over the endpoint the segment reaches —
finding 19's shape — because `WalkInv` binds neither register.

**The invariant's cursor pin is settled but not landed.**
`next_ge : G.next0 + stage2BootstrapExtent ≤ s.next` (`stage2BootstrapExtent := 28`,
the end of `entry`'s four `alloca`s) with the frame at
`walkPresent G C ++ [(G.next0, s.next - G.next0)]`.  It is *verified at the clause
and at `JsonStage2WalkScope`'s ten construction sites* — that module built green with
it — and unlanded because the six helper transfers whose target state is a parameter
`s₁` (`pureCore`, `pureJumpCore`, `pureCoreCarried`, `callQuiet`, `callQuietBr`,
`callQuietBrPending`) need a new hypothesis each and 70 call sites to pass it, in one
pass.  The handoff's Gap 1 has the measurements; do not re-derive them.

**The fifteen-block segment is still a supplied field of this bundle; ten of its
links are now a composition.**  The composition runs from the head to
`LeafBlock29`'s state: `strPath5` (links 1–5), `strPath8` (to `if.end256.i`,
links 6–8) and `strPath10` (to `NodeBlock31`'s target, links 9–10), each pinned
at `[propext, Classical.choice, Quot.sound]`.  Every intermediate state is a
`def` (`strS₁`–`strS₁₀`), every carry is the named `strC₁`–`strC₁₀`, and each
link's target carry is identified with its `abbrev` where it is used.

What the composition still takes splits in two.  **Link 9's call** is the seam:
its answer `r`, its answer's word and its six memory clauses are one premise
(residue R1), because the layer states no producer of the string body's staging
*at the call's own memory*; `harr`, `hcreg`, `hxpreg`, `hnxpreg` are the four
registers `walkStaticRegs` omits (`%arrayidx10.i`, `%c.i`, `%xp`, `%nxp`), read at
the state link 8 leaves; `hreadAr` is R5 (the log's `%z + 40` word) and `hGdst`
R6.  **Link 10's edge** takes R8.  The write-back links (11–15) are not composed
yet, so `HstringFacts.seg` stays the bundle's field and the composition's endpoint
is `LeafBlock29`'s state, not the merge.

**What the arm reads.**  `WalkDispatchResult.ofStringMerge` reads six of the
bundle's fields: the segment, its endpoint's block, index and predecessor, G9's two
endpoint cells, and G2's count test (`hcount`, without which there is no
`k2 ≤ nepv.toNat` for the merge's `hcap`).  G1 and G3–G8 are **not** read by the
arm.  They are the premise set a composition needs — the fifteen links' hypotheses,
grouped and stated at the head where they are true of the run — so they are the
target of the producer that would retire the supplied segment, and a refactor that
finds them unread and deletes them would delete that target.

**The blockers, named — and which is now only a parameter.**  The link's register
set (`%c.i`, `%xp`, `%nxp`, `%arrayidx10.i`) is carried by `strPath10`, because
`walkStaticRegs` omits them; adding them to the carrier is the measured 39-site
`WalkInv`-vocabulary change that `WalkMergeCells` and the continuing bundle's two
cursor cells would need as well.  Its six memory clauses are one premise (R1)
whose producer is named, not proved, because the two frame lemmas carrying
`s2StringBody_framed` from `s2StringBodyFoot` to `walkWide` are absent from this
layer; `s2StringBodyPre_at_string_call` (`JsonStage2StringStageFacts`) now
assembles the callee's precondition at this argument list, so the staging half no
longer blocks.  The allocator-cursor pin `C.alen ≤ G.ndst0 + ix.toNat` stays the
bundle's `hcur` at the head, which is where `pending = none`.

The link's `%xj.i` is the staging's address, `G.next0 + 12`; an earlier statement
of it had `+ 16`, where `s2StringBodyPre`'s `RegionsApart xj 8 outn 8` fails
against `%outn.i = G.next0 + 20`, so that earlier statement was uninhabited and
the census row that called the link proved records a proof, not an inhabitant.
The repair is at the link, and the composition uses the repaired statement.

A `WalkSegment` is not a bundle field in the composed design for one reason: a
field that *is* the merge arm's segment would make the bundle a restatement of
the arm it produces, so the bundle would be green whenever the arm is and say
nothing.  Here the segment is supplied because the composition is what is
missing, and the header says so rather than implying otherwise.

### Where the facts come from

| group | subject | source |
|---|---|---|
| G1 | the head's byte `%8` | **produced** — `h8` is `WalkInv.iter.reg8`; the three class bits are **the document's** (`entryByte G C.k`, a property of `G.bs` at `entryPos G C.k`, which neither the invariant nor the staging fixes) |
| G2 | the counts `%inc.i`, `%nep` | **produced** — `%inc.i` is the header's one binding `%k.0.i249 + 1` and `%nep` a parameter no block rebinds; the test's value is **the document's** count at the head (`C.k + 1 < G.nep`, the continuing arm) |
| G3 | the two-entry advance | **produced** where it is the invariant's (`%5`'s pointer is `WalkPtrs`; `%4`'s word and the head's bounds are the staging's), **the document's** for the lane read (`G.ent`'s word at the entry, `q = entryPos G (C.k + 1)`) |
| G4 | the value-position call | **supplied**: the root-done word's value, `s2ValuePosPre` and the callee's return are the callee's contract's, for which the tree states no producer at the call's argument list; `%root_done.i`'s pointer is **produced** (`walkStaticRegs`), and `C.sp = 0` is the arm's selector |
| G5 | the callee-success bit | **supplied** — the bit `%call222.i ≠ 0` is read off the callee's return word (G4's `xv`) |
| G6 | the arena reservation | **supplied**: `%idxprom.i`'s value and `%sub260.i`'s extent are the header's/`if.end207.i`'s cells, so the two tying equations and the cursor pin are the caller's; the log's arena word read and the capacity word are **produced** by `WalkInv.log_alen`/`log_acap` (as an inequality and a staged word) |
| G7 | the string body's call | **supplied**: the string body's staging — `s2StringBodyPre` at this argument list — has no producer in the tree, and `C.alen + ext ≤ G.n` is the reservation's document room |
| G8 | the verdict and the record | **supplied**: the callee's return word, `%outn.i`'s word (the decoded length, which `s2StringBodyPost` leaves free of the input length — `JsonStage2WalkArenaWord`); **produced** by the invariant for `%7` (`iter.reg7`) and the two log words (`log_len`, `log_cap`) |
| G9 | the segment and the merge's cells | **supplied** — `WalkSegment` records a run and an invariant, not the blocks it passed, so no lemma carries `%inc208.i` from `if.end207.i` to the merge; `%nep` is no `WalkInv` clause either.  Both are fields at the bundle's own endpoint `sd`; a `∀` over the states at `cleanup478.i` was the first shape and had no inhabitant |

Two of the supplied groups are supplied for a reason that is not a missing
lemma but a vocabulary gap, and the header keeps them distinct: G9's two cells are
the same gap `WalkMergeCells` (`JsonStage2WalkPremisesOfStaging`) records
(a segment carries no register-preservation step), and G4/G7's call preconditions
are the helper contracts' own staging, which is what a producer of
`s2ValuePosPre`/`s2StringBodyPre` supplies.  Nothing above is weakened to make a
proof go through: every field is either the invariant's clause read at `s`, a
property of the document, or a named supplied premise.

**Why the fields are stated at the head.** G1–G8's fields are stated at the head state `s` (and at `s.mem`/`s.next` for the
memory and the allocator cursor), which is where they are true of the run: the
intervening blocks read those cells rather than rebind them (`%8`, `%inc.i`,
`%nep`, `%4`, `%root_done.i`, `%idxprom.i`, `%7`, the log's words), and the
run's writes are separated from the log's cursor slot and the document.

**The reconciliation to each consuming link's own state is *not* carried by the
supplied segment, and cannot be.**  `WalkSegment` (`JsonStage2WalkTraverse`) is a
`run : ∀ n, runFuel … = runFuel …` and an `inv' : WalkInv G C' s'` — no memory, no
allocator cursor, no intermediate state.  So `hpreS` (the string body's
precondition at `s.mem`/`s.next`), `hreadA` (the log's arena word), `houtn` and
the log's two words are statements about the **head's** memory, and a composition
would have to transport each to the block that reads it: the cursor's advance
through the value-position call, the record's store at `%z.val`, and the two
calls' memories and allocator cursors.  That transport is a piece of work in its
own right — it is why the group's sources are named individually — and stating the
fields at the head is what keeps it visible instead of hiding it behind a segment
that does not carry it.

-/

import LeanLLVM.Refinement.JsonStage2WalkCall
import LeanLLVM.Refinement.JsonStage2WalkPhi
import LeanLLVM.Refinement.JsonStage2WalkSteps
import LeanLLVM.Refinement.JsonStage2WalkStore
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun
import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The unsigned test at one

The count's test is a `BitVec.ult`; the merge's price and the arm's `hcap` are
`Nat` statements.  This is the reading between them, proved here because the
layer's copy (`JsonEscapeDecodeRun.evalICmp_ult_one_iff`) is on the escape
side of the tree and the walk modules do not import it. -/

/-- **`icmp ult` is 1 exactly when the left operand's `toNat` is smaller.** -/
theorem walkEvalICmp_ult_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (1 : BitVec 1) ↔ x.toNat < y.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult x y
  · have h : ¬ x.toNat < y.toNat := by
      intro hlt
      have htrue : BitVec.ult x y = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : x.toNat < y.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-! ### The merge's two `phi`s on the string's edge

`cleanup478.i`'s depth and index phis both take their `if.else334.i` operand from
the same edge, and neither is a `phiIncoming` the layer has read yet: the depth's
is `%sp.i.0248` (unchanged through `s2_after_value`) and the index's is
`%inc208.i`, the word `if.end207.i` formed as `%k.0.i249 + 2`.  Named here because
the arm's two `hkOp`/`hsp` slots are exactly these, and a closed `decide` at the
call site would hide which edge it read. -/

/-- The merge's depth `phi` on the `if.else334.i` edge. -/
theorem stringCleanupSpIncoming_at :
    phiIncoming "if.else334.i" cleanupSpIncoming = some (Operand.reg "%sp.i.0248") := by
  decide

/-- The merge's index `phi` on the `if.else334.i` edge: the two-entry advance. -/
theorem stringCleanupKIncoming_at :
    phiIncoming "if.else334.i" cleanupKIncoming = some (Operand.reg "%inc208.i") := by
  decide

/-- `if.end245.i`'s `%key.1.i` phi takes `imm 0` on the `if.then219.i` edge — the
depth-zero entry's key bit.  It is why the path reaches `if.else334.i`
(`if.then328.i`'s `keyBit = 0` arm) and not `if.then330.i`, and it is the fact a
composition of the fifteen links reads at position 7.

The incoming list is the IR's own (`JsonStage2IR`'s `if.end245.i`), and nothing calls
this yet: the composition's key-zero branch is what will read it.  A change to that
block's `phi` would leave this stating a phantom of the literal it `decide`s, so a
composition should read it against the pinned AST rather than trust the list. -/
theorem if_end245_key_then219 :
    phiIncoming "if.then219.i"
      [("if.then231.i", (Operand.reg "%or.cond.i")),
       ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
       ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] =
      some (.imm (.int 1 (BitVec.ofNat 1 0))) := by
  decide

/-! ### The bundle -/

/-- **The two-entry token's facts.**  A standalone string consumes the opener and
the closer, so its merge index is `C.k + 2` and the continuing bundle
(`HcontFacts`), whose index is `C.k + 1`, is uninhabited at it.  This is the
input's facts at that head state, grouped by subject; each group's first member
is the witness the rest are stated at, and each group names the link that reads
it.

The segment is a field here — see the module header: the composition has landed
through link 10 (`strPath10`), and the write-back links (11–15) are what keeps the
field until they compose too. -/
structure HstringFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- **G1 — the head's byte.**  `%8` is `entryByte G C.k` (`WalkInv.iter.reg8`),
  and the three class bits say it is a `"` under both class bounds; they are read
  by `NodeBlock21_at` (`< 91`), `NodeBlock5_at` (`< 44`) and `LeafBlock_at`
  (`= 34`).  The bits are **the document's**: a property of `G.bs`'s byte at the
  entry's position, which the staging does not fix. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1
  hlt44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1
  heq34 : evalICmp .eq x (BitVec.ofNat 8 34) = 1
  /-- **G2 — the counts.**  `%inc.i` is the header's one binding of
  `%k.0.i249 + 1` and `%nep` is a parameter no block rebinds, so the two
  registers are `C.k + 1` and `G.nep` at the head; the test's value `1` is the
  continuing arm, which is what makes this token's branch the *wrong* one for
  its index (`sw_bb202_i_at`). -/
  hinc : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
  hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))
  hcount : evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 1
  /-- **G3 — the two-entry advance.**  `if.end207.i` reads the entry stream's
  *next* lane at `%5 + (%inc.i)·4`, forms `%inc208.i = %inc.i + 2` and branches
  `%4 > lane`; the lane is the closer's position, `entryPos G (C.k + 1)`, and it
  is **the document's** (`G.ent`'s word).  `%5` and `%4`'s value are the
  staging's. -/
  ep : Nat
  h5 : lookupName s.env "%5" = some (.ptr ep)
  bs : List UInt8
  hreadLane : readBytes s.mem (ep + (C.k + 1) * 4) 4 = some bs
  q : Nat
  hbs : bytesToNat bs = q
  hq : q = entryPos G (C.k + 1)
  h4 : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n))
  hk63 : C.k + 1 < 2 ^ 63
  hk64 : C.k + 2 < 2 ^ 64
  /-- **G4 — the value-position call.**  `if.then219.i` passes the depth and the
  root-done word to `s2_value_pos`; the pointer is the invariant's
  (`walkStaticRegs`'s `%root_done.i`), the word, the precondition and the
  callee's answer are **supplied** — no producer of `s2ValuePosPre` at this
  argument list is stated in the tree — and `C.sp = 0` is the arm's selector: at depth zero the block goes to
  `if.end245.i`, not to `land.lhs.true.i`. -/
  root : Nat
  hroot : lookupName s.env "%root_done.i" = some (.ptr root)
  rd : BitVec 32
  hreadRoot : readBytes s.mem root 4 = some (natToBytes rd.toNat 4)
  hsp0 : C.sp = 0
  hpreV : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next
  xv : BitVec 32
  hxv : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r →
    r.ret = .int 32 xv
  /-- **G5 — the callee's success bit.**  `if.end245.i`'s `%or.cond523.i` is
  `%key.1.i` (which the `if.then219.i` edge sets to `0`) selected against
  `%call222.i ≠ 0`, so the edge to `if.end256.i` is taken exactly when the
  callee's answer is not zero.  A non-zero answer is what the `s2_value_pos`
  contract returns on success. -/
  hbranch : evalICmp .ne xv (BitVec.ofNat 32 0) = 1
  /-- **G6 — the arena reservation.**  `%idxprom.i` is the token's position and
  `%sub260.i` the extent the reservation is made for, `entryPos G (C.k+1) - ix - 1`
  — the *tying equation*, which is what keeps this bundle from carrying two
  fields that cannot both hold (`HcontFactsOfStaging` records that defect in the
  continuing bundle's neighbourhood).  The cursor pin `C.alen ≤ G.ndst0 + ix` is
  **supplied**: `pending = none` at a loop head, so it is not invariant-carried.
  The arena word and the capacity word are the invariant's (`log_alen`'s witness,
  `log_acap`). -/
  ix : BitVec 64
  hix : lookupName s.env "%idxprom.i" = some (.int 64 ix)
  hixPos : ix.toNat = entryPos G C.k
  ext : Nat
  hext : ext = entryPos G (C.k + 1) - ix.toNat - 1
  hcur : C.alen ≤ G.ndst0 + ix.toNat
  A : BitVec 64
  hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8)
  Cc : BitVec 64
  hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8)
  hCc : natToBytes Cc.toNat 8 = wordBytes 8 G.dstcap
  /-- **G7 — the string body's call.**  The record's pointer, the document body
  after the opener, the extent, the arena's destination at the word `A`, the
  decoded-length slot, the position list and the two cursor words.
  **This is a supplied premise, not produced**: `s2StringBodyPre`'s producer is
  the string body's staging, which the tree does not yet state.

  **The `%xj.i` argument is stated at `G.next0 + 12`, not at `+ 16`.**  The
  staging fixes `%xj.i` at `G.next0 + 12` (`walkStaticRegs`), the neighbouring
  slots are `%root_done.i` at `G.next0 + 8` (four bytes) and `%outn.i` at
  `G.next0 + 20`, and `s2StringBodyPre` requires `RegionsApart xj 8 outn 8` —
  which is false at `+ 16` against `G.next0 + 20` (`16 + 8 > 20`).  The link
  `WalkLink.z_arena_reserve_exit` states the same argument at `+ 16` and its
  `hxj` at `%xj.i = G.next0 + 16`; as written that link's hypotheses are
  unsatisfiable together with `WalkInv.regs`, which is one of the reasons the
  segment is supplied here. -/
  hpreS : s2StringBodyPre
    [.ptr C.stage.c, .ptr (G.b + ix.toNat + 1), .int 64 (BitVec.ofNat 64 ext),
     .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
     .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next
  hwin : C.alen + ext ≤ G.n
  /-- **G8 — the verdict and the record.**  The body's answer is `NodeBlock31`'s
  and `LeafBlock29`'s `%call272.i`; `%7` is the entry's position (the literal
  arm's `%add283.i` reads it), `%outn.i`'s word is the decoded length the
  write-back loads (`if.else285.i`), and the log's `%len`/`%cap` words are what
  `if.end290.i` tests thirteen bytes against.  The answer, the decoded length
  and the two words' *values* are supplied; `%7` and the two log words are the
  invariant's clauses read at the head. -/
  y : BitVec 32
  hy : ∀ r, stage2Calls stage2SubCalls "s2_string_body"
    [.ptr C.stage.c, .ptr (G.b + ix.toNat + 1), .int 64 (BitVec.ofNat 64 ext),
     .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
     .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r →
    r.ret = .int 32 y
  h7 : lookupName s.env "%7" = some (.int 32 (BitVec.ofNat 32 (entryPos G C.k)))
  outn : Nat
  houtn : readBytes s.mem (G.next0 + 20) 8 = some (wordBytes 8 outn)
  hnl : readBytes s.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen)
  hnc : readBytes s.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)
  /-- **G9 — the segment and the merge's cells.**  The path is supplied whole,
  because the write-back links are not composed yet (`strPath10` reaches
  `LeafBlock29`'s state), and with it the endpoint's block, index and
  predecessor.  The two cells are the merge's on the `if.else334.i`
  edge, where `cleanupKIncoming` selects `%inc208.i` and `%nep` is the register
  the merge tests.

  **They are fields at this bundle's own endpoint** (`sd`), not a `∀` over the
  states the invariant pins at `cleanup478.i`.  A `∀` was the first shape here and
  it had no inhabitant: `WalkInv` binds neither `%inc208.i` nor `%nep`
  (`walkStaticNames` names neither), so at any other state at that block with that
  predecessor either register is free, and a field that fixes them all is false.
  Stating them at `sd` costs nothing — the endpoint is a field — and it is the same
  shape `HlastFacts` uses for its two cells. -/
  Cd : WalkCarry G
  sd : State
  seg : WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 15
  hsegBlock : Cd.block = "cleanup478.i"
  hsegK : Cd.k = C.k
  hsegPre : sd.pre = some "if.else334.i"
  hinc208 : lookupName sd.env "%inc208.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 2)))
  hnepM : lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))

/-! ### The segment, as the bundle names it

The conclusion the composed version states, read off the supplied field: the
endpoint's block, index and predecessor, and the invariant at it.  Its only
content is the bundle's own field, and the docstring says so rather than
claiming a composition. -/

/-- **The two-entry token's path to the merge.**  The segment is
`HstringFacts.seg`, whose composition has landed through link 10 (`strPath10`)
with the write-back links still owed; this lemma is the shape a consumer reads, so
the fact that the segment is supplied is at the field, not at every call site. -/
theorem stringPath_seg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HstringFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 15 ∧
      Cd.block = "cleanup478.i" ∧ Cd.k = C.k ∧
      sd.pre = some "if.else334.i" ∧ WalkInv G Cd sd :=
  ⟨f.Cd, f.sd, f.seg, f.hsegBlock, f.hsegK, f.hsegPre, f.seg.inv'⟩

/-! ### The merge arm

The arm `standaloneString_finish` states as an outcome, as a
`WalkDispatchResult`: the merge at `k2 = C.k + 2` and `%nep = G.nep`, the depth
the invariant carries, and the price `15 + 2 ≤ 32·2 + 8·(entryPos G (C.k+2) −
entryPos G C.k)`, which the two-entry advance alone pays. -/

/-- **The `merge` arm from the two-entry bundle.**  The dispatch reaches
`cleanup478.i` at `%k.2.i = %inc208.i = %k.0.i249 + 2`, so the index advanced by
two and the entry count is `G.nep`; the classification is the merge's own test
on that index (`WalkDispatchResult.toOutcome`), which at `C.k = 0`,
`G.nep = 2` reads `2 < 2` — false — and gives the `finish` the standalone string
is.  No premise tests `C.k + 1 < G.nep` here: that test is the head's, and it is
what selects *which bundle* describes the state, not what the dispatch does. -/
theorem WalkDispatchResult.ofStringMerge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (f : HstringFacts G C s) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  have hnep64 : G.nep < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
  -- the header's word reads back as the header's index: the index is inside the
  -- document, so the cast does not wrap
  have hk64 : C.k + 1 < 2 ^ 64 := by
    have h1 := hInv.k_le
    have h2 := G.nep_le
    have h3 := G.maxDoc
    simp only [stage2MaxDocument] at h3
    omega
  have hincv : (BitVec.ofNat 64 (C.k + 1)).toNat = C.k + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  -- the continuing test, read as the two counts' order
  have hk1 : C.k + 1 < G.nep := by
    have h := (walkEvalICmp_ult_one_iff (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep)).1 f.hcount
    rw [hincv, hnepv] at h
    exact h
  have hk2cap : C.k + 2 ≤ G.nep := by omega
  refine WalkDispatchResult.merge f.Cd f.sd 15 f.Cd.sp (C.k + 2) "if.else334.i"
    (Operand.reg "%sp.i.0248") (Operand.reg "%inc208.i") (BitVec.ofNat 64 G.nep)
    f.seg f.hsegBlock f.hsegK f.hsegPre ?_ ?_ ?_ ?_ f.hnepM ?_ ?_ ?_ ?_ ?_
  · -- the merge's depth `phi` takes `%sp.i.0248` on the `if.else334.i` edge
    exact stringCleanupSpIncoming_at
  · -- and that register is the depth the endpoint's invariant carries
    exact f.seg.inv'.depth_reg
  · -- the merge's index `phi` takes `%inc208.i` on the same edge
    exact stringCleanupKIncoming_at
  · -- the two-entry advance, at the word `if.end207.i` wrote
    exact f.hinc208
  · -- the index advanced
    omega
  · rw [hnepv]
    exact hk2cap
  · exact f.seg.inv'.depth_cap
  · exact f.seg.inv'.sp_le_wlen
  · -- the price: the entry term alone pays it, and the byte term is a `Nat`, so
    -- no `entryPos` monotonicity and no terminal-index law is read
    show 15 + 2 ≤ stage2EntryAllowance * (C.k + 2 - C.k) +
      stage2ByteAllowance * (entryPos G (C.k + 2) - entryPos G C.k)
    simp only [stage2EntryAllowance, stage2ByteAllowance]
    omega

/-! ### The continuing branch's two cases

`walkLoopStep_of_staging`'s continuing branch needs the bundle that describes the
state.  There are two: the one-entry token's (`HcontFacts`, indexed at
`C.k + 1`) and the two-entry token's (`HstringFacts`, at `C.k + 2`).  This is
their disjunction, so the `rcases` at the call site is one line and the
classification stays the merge's. -/

/-- **The continuing branch's bundle is one of the two tokens'.**  The one-entry
case is the whitespace scan's (`HcontFacts`); the two-entry case is the
standalone string's, whose merge index overshoots the head's test.  Both arms
produce a `WalkDispatchResult` — the first through the revolution's segment, the
second through `WalkDispatchResult.ofStringMerge` — so the case is named here
rather than decided by the head's index.

**The arms are disjoint at a state**, which is what makes this a class rather than a
fan-out: `HcontFacts.hlt91` says the head's byte is *not* below `91`, and
`HstringFacts.heq34` says it *is* `34`; no state satisfies both, so a producer that
reads the head's byte answers with one arm and the consumer's two branches never
overlap. -/
inductive HcontCase {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type
  /-- The continuing entry ends inside its entry and the merge index is
  `C.k + 1`: `HcontFacts` at the head state. -/
  | ws : HcontFacts G C s → HcontCase G C s
  /-- The token is a standalone string: two entries consumed, merge index
  `C.k + 2`, and `HstringFacts` at the head state. -/
  | twoEntry : HstringFacts G C s → HcontCase G C s

/-! ### The fifteen links, composed

`HstringFacts.seg` is the last piece of the two-entry token that is *supplied*
rather than proved, and this section is the composition that retires it.  The
fifteen links are the module header's table; what a composition owes beside them is
the *states* they reach — a link's target state must be nameable before the next
link's hypotheses can be stated at it — and the handful of facts no clause of
`WalkInv` carries at the state that reads them.

**The states are `def`s.**  `strSₙ` is the state the `n`-th link reaches, written
from the previous link's state rather than restated: `strS₅` is `if.end207.i`'s
target at `strS₄`'s state.  The alternative — spelling each link's target term at
each use — is the defect `HlastFacts`' producer records: a state that is not named
cannot be read at, and a fact stated at a name the run never occupies is vacant.

**The carries are named too.**  The path changes the carry at four points only
(`if.end256.i` sets the record in flight, `z_arena_reserve.exit` spends it,
`if.then328.i` appends the record, `if.else334.i` advances the state map), so
`strCₙ` is the carry the `n`-th link reaches and the four changes are visible
there rather than in a chain of anonymous updates.
-/

/-! #### The carries -/

/-- The carry after `NodeBlock21`. -/
abbrev strC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock5" }

/-- The carry after `NodeBlock5`. -/
abbrev strC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { strC₁ C with block := "LeafBlock" }

/-- The carry after `LeafBlock`. -/
abbrev strC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { strC₂ C with block := "sw.bb202.i" }

/-- The carry after `sw.bb202.i`. -/
abbrev strC₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { strC₃ C with block := "if.end207.i" }

/-- The carry after `if.end207.i`. -/
abbrev strC₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { strC₄ C with block := "if.then219.i" }

/-- The carry after `if.then219.i`. -/
abbrev strC₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { strC₅ C with block := "if.end245.i" }

/-- The carry after `if.end245.i`. -/
abbrev strC₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { strC₆ C with block := "if.end256.i" }

/-- **The carry after `if.end256.i`**: the record in flight is the triple the
check reads — the token's position, the arena's cursor and its extent. -/
abbrev strC₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) : WalkCarry G :=
  { (strC₇ C) with
    block := "z_arena_reserve.exit",
    pending := some (ix.toNat, C.alen, ext) }

/-- **The carry after `z_arena_reserve.exit`**: the cursor spends the reservation
and the window joins the spans, which is where the carry parts company with the
memory's `%alen` word. -/
abbrev strC₉ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) : WalkCarry G :=
  { (strC₈ C ix ext) with
    block := "NodeBlock31",
    alen := C.alen + ext,
    spans := C.spans ++ [(C.alen, ext)],
    pending := none }

/-- The carry after `NodeBlock31`. -/
abbrev strC₁₀ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) : WalkCarry G :=
  { (strC₉ C ix ext) with block := "LeafBlock29" }

/-- The carry after `LeafBlock29`: the arm is the answer's own test, so the two
continuations are one carry name and the case is taken at the link. -/
abbrev strC₁₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) (y : BitVec 32) : WalkCarry G :=
  { (strC₁₀ C ix ext) with
    block := (if evalICmp .eq y (BitVec.ofNat 32 1) = 1 then "if.then281.i"
      else "if.else285.i") }

/-- The carry after `if.then281.i` or `if.else285.i` — the arms converge on one
merge, so this is one name for both. -/
abbrev strC₁₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) (y : BitVec 32) : WalkCarry G :=
  { (strC₁₁ C ix ext y) with block := "if.end290.i" }

/-- The carry after `if.end290.i`: the reserve test is the edge, so the block is
the test's own value. -/
abbrev strC₁₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) (y : BitVec 32) (nl nc : BitVec 64) : WalkCarry G :=
  { (strC₁₂ C ix ext y) with
    block := (if evalICmp .ugt (nl + BitVec.ofNat 64 13) nc = 1 then "if.end.i86"
      else "if.then328.i") }

/-- **The carry after `if.then328.i`**: the record joins the trace and the event
cursor advances by its width. -/
abbrev strC₁₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) (y : BitVec 32) (nl nc : BitVec 64) (keyBit : BitVec 1)
    (sinkIn span : BitVec 64) : WalkCarry G :=
  { (strC₁₃ C ix ext y nl nc) with
    block := (if keyBit = 1 then "if.then330.i" else "if.else334.i"),
    evlen := C.evlen + 13,
    events := C.events ++
      [EventRecord.str (keyBit = 1) (sinkIn.toNat % 2 ^ 32) span.toNat] }

/-- **The carry after `if.else334.i`**: the container's state map advances and the
run is at the merge. -/
abbrev strC₁₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) (y : BitVec 32) (nl nc : BitVec 64) (keyBit : BitVec 1)
    (sinkIn span : BitVec 64) : WalkCarry G :=
  { (strC₁₄ C ix ext y nl nc keyBit sinkIn span) with
    block := "cleanup478.i",
    stMap := walkAfterValueMap C }

/-! #### The states -/

/-- The state `NodeBlock21` reaches: `%Pivot22` and the edge to `NodeBlock5`. -/
def strS₁ (s : State) : State :=
  { (s.bind "%Pivot22" (.int 1 1)) with pc := "NodeBlock5", pre := some s.pc }

/-- The state `NodeBlock5` reaches. -/
def strS₂ (s : State) : State :=
  { ((strS₁ s).bind "%Pivot6" (.int 1 1)) with pc := "LeafBlock", pre := some (strS₁ s).pc }

/-- The state `LeafBlock` reaches: the byte is `"`, so the edge is the string arm. -/
def strS₃ (s : State) : State :=
  { ((strS₂ s).bind "%SwitchLeaf" (.int 1 1)) with
    pc := "sw.bb202.i",
    pre := some (strS₂ s).pc }

/-- The state `sw.bb202.i` reaches: the count test is the header's one-entry
advance, so its answer is `1` and the edge is `if.end207.i`. -/
def strS₄ (s : State) : State :=
  { ((strS₃ s).bind "%cmp203.not.i" (.int 1 1)) with
    pc := "if.end207.i",
    pre := some (strS₃ s).pc }

/-- The memory `if.end207.i` writes: the cursor record's `k` field, eight bytes at
`%k11.i = C.stage.c + 32`. -/
def strSetK₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (t : State) : State :=
  { t with mem := writeBytes t.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)) }

/-- **The state `if.end207.i` reaches.**  The two-entry advance writes the cursor
record's `k` field at `%k11.i = C.stage.c + 32`, loads the *next* lane and tests
the bound; `q` is the lane it read. -/
def strS₅ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q : Nat) (s : State) : State :=
  { stateAt (cells [
      ("%cmp212.not.i", .int 1 1),
      ("%conv211.i", .int 64 (BitVec.ofNat 64 q)),
      ("%25", .int 32 (BitVec.ofNat 32 q)),
      ("%arrayidx209.i", .ptr (G.ep + (C.k + 1) * 4)),
      ("%inc208.i", .int 64 (BitVec.ofNat 64 (C.k + 2)))] (strS₄ s).env)
      (strSetK₅ C (strS₄ s)) with
    pc := "if.then219.i",
    pre := some (strS₄ s).pc }

/-- **The state `if.then219.i` reaches.**  The depth is zero (`G4`'s `hsp0`), so
the edge is `if.end245.i` and not `land.lhs.true.i`; the three cells are the
depth's test, the callee's answer and the root word it returned.  The memory is
the caller's: `s2_value_pos` hands it back (`r.mem = mem`). -/
def strS₆ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q : Nat)
    (rd x : BitVec 32) (s : State) : State :=
  { stateAt (cells [
      ("%cmp223.not.i", .int 1 1),
      ("%call222.i", .int 32 x),
      ("%26", .int 32 rd)] (strS₅ G C q s).env) (strS₅ G C q s) with
    pc := "if.end245.i",
    pre := some (strS₅ G C q s).pc }

/-- **The state `if.end245.i` reaches.**  The `if.then219.i` edge's key bit is
`0` (the bundle's `if_end245_key_then219`), and the callee's answer is non-zero,
so the selected bit is `1` and the edge is `if.end256.i`; `%key.1.i` is `0` and
`%tobool248.i` is `1`. -/
def strS₇ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q : Nat)
    (rd x : BitVec 32) (s : State) : State :=
  { stateAt (("%or.cond523.i", .int 1 1) :: ("%tobool248.i", .int 1 1) ::
      ("%key.1.i", .int 1 0) :: (strS₆ G C q rd x s).env) (strS₆ G C q rd x s) with
    pc := "if.end256.i",
    pre := some (strS₆ G C q rd x s).pc }

/-- **The state `if.end256.i` reaches.**  The block's own target: `%sub260.i`,
the `%outn.i` zero, the two log words, the check's bit and the edge.  The block's
check is clear at the bundle's arithmetic (`walkArenaReserve_clear`), which the
composition reads to name the carry `strC₈`; the state keeps the edge as the block
computed it, so the name does not decide the arm. -/
def strS₈ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q : Nat)
    (rd x : BitVec 32) (A Cc ix : BitVec 64) (s : State) : State :=
  walkIfEnd256OutAt G (strC₇ C) (strS₇ G C q rd x s) A Cc (BitVec.ofNat 64 q) ix

/-- **The state `z_arena_reserve.exit` reaches.**  The callee's answered memory and
cursor, the four cells the block bound — the answer `%call272.i`, the two `gep`s
and the arena's base — and the edge into `NodeBlock31`.  The reservation's position
is `%idxprom.i`'s, which the carry's `pending` names. -/
def strS₉ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q : Nat)
    (rd x : BitVec 32) (A Cc ix : BitVec 64) (ext : Nat) (r : CallOutcome)
    (s : State) : State :=
  walkZArenaReserveExitOutAt G (strC₈ C ix ext)
    (strS₈ G C q rd x A Cc ix s) ix.toNat A r

/-- **The state `NodeBlock31` reaches.**  `icmp slt i32 %call272.i, 1` is `0`
(R8), so the edge is `LeafBlock29`; the cell is the pivot bit and the answer is
`%call272.i`'s, which the previous state bound to the callee's. -/
def strS₁₀ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q : Nat)
    (rd x : BitVec 32) (A Cc ix : BitVec 64) (ext : Nat) (r : CallOutcome)
    (s : State) : State :=
  { ((strS₉ G C q rd x A Cc ix ext r s).bind "%Pivot32" (.int 1 0)) with
    pc := "LeafBlock29",
    pre := some (strS₉ G C q rd x A Cc ix ext r s).pc }

/-! #### The root slot and the log across the cursor-record store

The links after `if.end207.i` read regions its store does not touch: the root slot
at `G.next0 + 8` (`if.then219.i`), and the log's words at `%z + 40`, `%z + 48`
and `%z + 56` (`if.end256.i` and `z_arena_reserve.exit`).  The store is the cursor
record's `k` field, eight bytes at `%k11.i = C.stage.c + 32`.  The record's own
extent ends at or below the cursor (`WalkStage.sevenEnd`), and the staging
separates the record from the log (`WalkStage.separate`), so both regions survive
it.

These are the crossings the composition of links 6–9 spends, and they name only
`WalkStage`, `State` and `readBytes` — which is why they live here rather than in
`JsonStage2WalkStringPath`: a module that imports this one cannot be used by it.

The log's *base* word (`%z + 40`) is still not a lemma's.  The staging gives the
object's presence (`WalkInv.owned`), not the value in it, and `WalkInv` binds only
`+8`, `+16`, `+32`, `+48` and `+56`; so the composition takes that word as a named
premise (residue R5) whose producer is the initialisation's store at `%z + 40` and
a `WalkInv` clause for the arena's base. -/

/-- **The cursor record ends at or below the call's cursor.** -/
theorem walkCursorRecord_end {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} :
    C.stage.c + stage2CursorExtent ≤ G.next0 :=
  C.stage.sevenEnd (C.stage.c, stage2CursorExtent) (by simp [stage2StagedWrites])

/-- **A read of the root slot survives `if.end207.i`'s cursor-record store.**
The store is eight bytes at `c + 32`; the cursor record's extent is `1192`, so the
store ends at `c + 40`, at or below the cursor, and the root slot begins at
`cursor + 8`. -/
theorem walkReadBytes_rootSlot_of_cursorK {m : Mem} {c next0 k : Nat}
    (hsep : c + stage2CursorExtent ≤ next0) :
    readBytes (writeBytes m (c + 32) (wordBytes 8 k)) (next0 + 8) 4
      = readBytes m (next0 + 8) 4 := by
  refine walkReadBytes_writeBytes_outside (start := c + 32) (addr := next0 + 8) (n := 4) ?_
  right
  have hlen : (wordBytes 8 k).length = 8 := natToBytes_length _ _
  simp only [stage2CursorExtent] at hsep
  rw [hlen]
  omega

/-- **The root slot's four bytes, read at the state `if.end207.i` leaves.**  The
head's read is the one `if.then219.i` needs: the store between them is the cursor
record's `k` field, and the root slot is above it.  No invariant is consumed — the
store's separation is `WalkStage.sevenEnd` at the staging the carry names — so the
fact is stated at the carry. -/
theorem walkReadBytes_rootSlot_at {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {k : Nat} {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4)) :
    readBytes (writeBytes s.mem (C.stage.c + 32) (wordBytes 8 k)) (G.next0 + 8) 4
      = some (natToBytes rd.toNat 4) := by
  rw [walkReadBytes_rootSlot_of_cursorK (c := C.stage.c) (next0 := G.next0)
    (walkCursorRecord_end (G := G) (C := C))]
  exact hread

/-- **The cursor record and the log are separate.**  Both are members of
`stage2StagedWrites`, so the staging's `DisjointRegions` separates them; the two
extents differ (`1192` against `64`), which is what makes the pair distinct. -/
theorem walkCursorLog_sep {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    S.c + stage2CursorExtent ≤ S.z ∨ S.z + stage2LogExtent ≤ S.c := by
  have hne : ((S.c, stage2CursorExtent) : Nat × Nat) ≠ (S.z, stage2LogExtent) := by
    intro heq
    exact absurd (Prod.mk.inj heq).2 (by decide)
  have h := disjointRegions_pair_of_mem (S.writes_separate)
    (r := (S.c, stage2CursorExtent)) (t := (S.z, stage2LogExtent))
    (by simp [stage2StagedWrites]) (by simp [stage2StagedWrites]) hne
  simpa using h

/-- **A log read survives `if.end207.i`'s cursor-record store.**  The store's
eight bytes at `c + 32` lie inside the cursor record, which the staging separates
from the log's `64` bytes at `z`; a read at an offset inside the log is therefore
outside the store. -/
theorem walkReadBytes_log_of_cursorK {m : Mem} {c z off w k : Nat}
    (hsep : c + stage2CursorExtent ≤ z ∨ z + stage2LogExtent ≤ c)
    (hsub : off + w ≤ stage2LogExtent) :
    readBytes (writeBytes m (c + 32) (wordBytes 8 k)) (z + off) w
      = readBytes m (z + off) w := by
  refine walkReadBytes_writeBytes_outside (start := c + 32) (addr := z + off) (n := w)
    (v := wordBytes 8 k) ?_
  rw [show (wordBytes 8 k).length = 8 from natToBytes_length _ _]
  simp only [stage2CursorExtent, stage2LogExtent] at hsep hsub ⊢
  rcases hsep with h | h
  · right; omega
  · left; omega

/-- **A word's `ofNat` at its own `toNat` is itself.**  The core's `ofNat_toNat`
is about `setWidth`, so the walk layer states the form it needs. -/
theorem walkOfNat_toNat {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- **`xor` with the all-ones word is the complement.**  The block's `%30` is
`%idxprom.i ^^^ -1`; at a position below `2 ^ 64` that word is `2 ^ 64 - 1 - p`,
which is what makes the token's extent read back as a natural subtraction. -/
theorem walkOfNat_xor_allOnes {w p : Nat} (hp : p < 2 ^ w) :
    BitVec.ofNat w p ^^^ BitVec.ofNat w (2 ^ w - 1)
      = BitVec.ofNat w (2 ^ w - 1 - p) := by
  have hall : (BitVec.ofNat w (2 ^ w - 1) : BitVec w) = BitVec.allOnes w := by
    apply BitVec.toNat_inj.mp
    rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes,
      Nat.mod_eq_of_lt (Nat.sub_one_lt (Nat.two_pow_pos w).ne')]
  rw [hall, BitVec.xor_allOnes]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- **`%sub260.i` is the token's extent.**  `if.end256.i` forms `%conv211.i + %30`
with `%30 = %idxprom.i ^^^ -1`; when the cursor's advance is `%conv211.i`'s one, the
subtraction does not wrap and the word is the extent.  The identity is the
composition's, not the link's: the link states the cell as the sum, and the state
that reads it needs the extent. -/
theorem walkSub260_eq {ix cv : BitVec 64} {ext : Nat}
    (hcv : cv.toNat = ix.toNat + ext + 1) :
    cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615) = BitVec.ofNat 64 ext := by
  have hxor : (ix ^^^ BitVec.ofNat 64 18446744073709551615)
      = BitVec.ofNat 64 (2 ^ 64 - 1 - ix.toNat) := by
    have h := walkOfNat_xor_allOnes (w := 64) (p := ix.toNat) ix.isLt
    simpa only [walkOfNat_toNat] using h
  rw [hxor, ← walkOfNat_toNat cv, hcv]
  bv_omega

/-- **`s2_value_pos` at depth zero answers from the depth alone.**  The block reads
nothing when the depth is zero (`stage2ValuePos`'s first arm), so its reply's
`ret` is independent of the memory and the cursor it is called with — which is what
transports the bundle's `hxv` from the head's memory to the state `if.end207.i`
leaves. -/
theorem s2ValuePosCall_ret_at_zero {mem mem' : Mem} {next next' : Nat}
    {sp rd : BitVec 32} {ct cs : Nat} {r r' : CallOutcome}
    (hsp : sp.toNat = 0)
    (h : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next = some r)
    (h' : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem' next' = some r') :
    r.ret = r'.ret := by
  have h1 : r = ⟨.int 32 (BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0)), mem, next⟩ := by
    rw [s2ValuePos_reply] at h
    simp only [stage2ValuePos, hsp, ↓reduceIte] at h
    exact Option.some.inj h.symm
  have h2 : r' = ⟨.int 32 (BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0)), mem', next'⟩ := by
    rw [s2ValuePos_reply] at h'
    simp only [stage2ValuePos, hsp, ↓reduceIte] at h'
    exact Option.some.inj h'.symm
  rw [h1, h2]

/-! #### The first five links

The four class-A blocks and the two-entry advance: no hypothesis here is beside the
head bundle's fields and `WalkInv`'s clauses, and the one memory write is
`if.end207.i`'s own cursor-record store, which the next link reads across. -/

/-- **`ult` is 1 exactly at the unsigned order**, read like `walkEvalICmp_ult_one_iff`. -/
theorem walkEvalICmp_ugt_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ugt x y = (1 : BitVec 1) ↔ y.toNat < x.toNat := by
  have h := walkEvalICmp_ult_one_iff (x := y) (y := x)
  simpa only [evalICmp] using h

/-- **`evalICmp .ugt` at two staged words**: `1` exactly when the right word's
`toNat` is below the left's, which below `2 ^ 64` is the words' own order. -/
theorem walkEvalICmp_ugt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : b < a) :
    evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  refine (walkEvalICmp_ugt_one_iff _ _).2 ?_
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact h

/-- **`evalICmp .ugt` at two staged words is `0`** when the left's `toNat` does
not exceed the right's: the companion `walkEvalICmp_ugt_ofNat` is missing.  The
arena's check is read through this at the reservation's arithmetic, where the
right word's `toNat` is `dstcap`. -/
theorem walkEvalICmp_ugt_ofNat_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a ≤ b) : evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0 := by
  rcases walkBitVec1_zero_or_one
    (evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) with h0 | h1
  · exact h0
  · exfalso
    have hlt := (walkEvalICmp_ugt_one_iff _ _).1 h1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hlt
    omega

/-- **The two-entry advance's lane is past the entry's own index** — the fact
`if.end207.i`'s bound test reads, from the stream's order and the position's
inside-ness. -/
theorem strLane_lt {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k + 1 < G.nep) :
    entryPos G k < entryPos G (k + 1) := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  have h1 : k < G.ent.length := by omega
  have h2 : k + 1 < G.ent.length := by omega
  have := List.pairwise_iff_getElem.mp G.order k (k + 1) h1 h2 (by omega)
  simpa only [entryPos, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] using this

/-- **The first five links compose.**  From the head to `if.then219.i`: the four
class-A branches, whose bytes and counts are the bundle's fields, and the two-entry
advance, whose lane read is the bundle's `hreadLane` and whose store is the cursor
record's own field. -/
theorem strPath5 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s) :
    ∃ s', WalkSegment (stage2Calls stage2SubCalls) G C s (strC₅ C) s' 5 ∧
      s' = strS₅ G C f.q s := by
  -- the header's count test: `C.k + 1 < G.nep`, which `if.end207.i`'s lane needs
  have hk64 : C.k + 1 < 2 ^ 64 := by
    have h1 := hInv.k_le; have h2 := G.nep_le; have h3 := G.maxDoc
    simp only [stage2MaxDocument] at h3
    omega
  have hincv : (BitVec.ofNat 64 (C.k + 1)).toNat = C.k + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hk1 : C.k + 1 < G.nep := by
    have h := (walkEvalICmp_ult_one_iff _ _).1 f.hcount
    rw [hincv, hnepv] at h
    exact h
  have hn64 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  -- 1. `NodeBlock21`
  obtain ⟨s1, hl1, hs1⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hhead f.h8
  have hs1' : s1 = strS₁ s := by
    rw [hs1, f.hlt91, if_pos rfl]
    dsimp only [strS₁, State.bind]
  have hcarry1 : ({ C with
      block := (if evalICmp .slt f.x (BitVec.ofNat 8 91) = 1 then "NodeBlock5"
        else "NodeBlock19") } : WalkCarry G) = strC₁ C := by
    rw [f.hlt91, if_pos rfl]
  subst hs1'
  have hl1' : WalkLink (stage2Calls stage2SubCalls) G C s (strC₁ C) (strS₁ s) := by
    rw [← hcarry1]; exact hl1
  -- 2. `NodeBlock5`: the byte is the head's (`%8` is not rebound)
  have h8₂ : evalOperand (strS₁ s) (.reg "%8") = some (.int 8 f.x) := by
    simp only [strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact f.h8
  obtain ⟨s2, hl2, hs2⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (strC₁ C) (strS₁ s)
      hl1'.inv' rfl h8₂
  have hs2' : s2 = strS₂ s := by
    rw [hs2, f.hlt44, if_pos rfl]
    dsimp only [strS₂, strS₁, State.bind]
  have hcarry2 : ({ strC₁ C with
      block := (if evalICmp .slt f.x (BitVec.ofNat 8 44) = 1 then "LeafBlock"
        else "NodeBlock") } : WalkCarry G) = strC₂ C := by
    rw [f.hlt44, if_pos rfl]
  subst hs2'
  have hl2' : WalkLink (stage2Calls stage2SubCalls) G (strC₁ C) (strS₁ s)
      (strC₂ C) (strS₂ s) := by
    rw [← hcarry2]; exact hl2
  -- 3. `LeafBlock`: the byte is `"`, so the edge is the string arm
  have h8₃ : evalOperand (strS₂ s) (.reg "%8") = some (.int 8 f.x) := by
    simp only [strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact f.h8
  obtain ⟨s3, hl3, hs3⟩ :=
    WalkLink.LeafBlock_at (calls := stage2Calls stage2SubCalls) G (strC₂ C) (strS₂ s)
      hl2'.inv' rfl h8₃
  have hs3' : s3 = strS₃ s := by
    rw [hs3, f.heq34, if_pos rfl]
    dsimp only [strS₃, strS₂, strS₁, State.bind]
  have hcarry3 : ({ strC₂ C with
      block := (if evalICmp .eq f.x (BitVec.ofNat 8 34) = 1 then "sw.bb202.i"
        else "sw.default.i") } : WalkCarry G) = strC₃ C := by
    rw [f.heq34, if_pos rfl]
  subst hs3'
  have hl3' : WalkLink (stage2Calls stage2SubCalls) G (strC₂ C) (strS₂ s)
      (strC₃ C) (strS₃ s) := by
    rw [← hcarry3]; exact hl3
  -- 4. `sw.bb202.i`: the count test is the header's one-entry advance
  have hinc₄ : evalOperand (strS₃ s) (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    simp only [strS₃, strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%inc.i") _ _ (by decide)]
    exact f.hinc
  have hnep₄ : evalOperand (strS₃ s) (.reg "%nep") =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    simp only [strS₃, strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%nep") _ _ (by decide)]
    exact f.hnep
  obtain ⟨s4, hl4, hs4⟩ :=
    WalkLink.sw_bb202_i_at (calls := stage2Calls stage2SubCalls) G (strC₃ C) (strS₃ s)
      hl3'.inv' rfl hinc₄ hnep₄
  have hs4' : s4 = strS₄ s := by
    rw [hs4, f.hcount, if_pos rfl]
    dsimp only [strS₄, strS₃, strS₂, strS₁, State.bind]
  have hcarry4 : ({ strC₃ C with
      block := (if evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 1
        then "if.end207.i" else "if.then205.i") } : WalkCarry G) = strC₄ C := by
    rw [f.hcount, if_pos rfl]
  subst hs4'
  have hl4' : WalkLink (stage2Calls stage2SubCalls) G (strC₃ C) (strS₃ s)
      (strC₄ C) (strS₄ s) := by
    rw [← hcarry4]; exact hl4
  -- 5. `if.end207.i`: the advance, the lane read and the cursor-record store
  have hep : f.ep = G.ep := by
    have h5 : some (Value.ptr f.ep) = some (Value.ptr G.ep) :=
      f.h5.symm.trans hInv.ptrs.2.1
    exact Value.ptr.inj (Option.some.inj h5)
  have hinc₅ : lookupName (strS₄ s).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    simp only [strS₄, strS₃, strS₂, strS₁, State.bind,
      lookupName_cons_ne (k := "%cmp203.not.i") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%inc.i") _ _ (by decide)]
    exact f.hinc
  have h4₅ : lookupName (strS₄ s).env "%4" =
      some (.int 64 (BitVec.ofNat 64 G.n)) := by
    simp only [strS₄, strS₃, strS₂, strS₁, State.bind,
      lookupName_cons_ne (k := "%cmp203.not.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%4") _ _ (by decide)]
    exact f.h4
  have hread₅ : readBytes (strS₄ s).mem (G.ep + (C.k + 1) * 4) 4 = some f.bs := by
    have := f.hreadLane
    rw [hep] at this
    simpa only [strS₄, strS₃, strS₂, strS₁, State.bind] using this
  have hqlt : f.q < G.n := by
    rw [f.hq]
    exact entryPos_lt G (by omega)
  have hbit₅ : evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 f.q) = 1 :=
    walkEvalICmp_ugt_ofNat hn64 (by omega) hqlt
  obtain ⟨s5, hl5, hs5⟩ :=
    WalkLink.if_end207_i (calls := stage2Calls stage2SubCalls) G (strC₄ C) (strS₄ s)
      hl4'.inv' rfl f.hk63 hinc₅ h4₅ hread₅ f.hbs f.hk64
  have hs5' : s5 = strS₅ G C f.q s := by
    rw [hs5, hbit₅, if_pos rfl]
    dsimp only [strS₅, strSetK₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt, cells]
  have hcarry5 : ({ strC₄ C with
      block := (if evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 f.q) = 1
        then "if.then219.i" else "if.then214.i") } : WalkCarry G) = strC₅ C := by
    rw [hbit₅, if_pos rfl]
  subst hs5'
  have hl5' : WalkLink (stage2Calls stage2SubCalls) G (strC₄ C) (strS₄ s)
      (strC₅ C) (strS₅ G C f.q s) := by
    rw [← hcarry5]; exact hl5
  exact ⟨_, ((((WalkSegment.of_link hl1').trans (WalkSegment.of_link hl2')).trans
    (WalkSegment.of_link hl3')).trans (WalkSegment.of_link hl4')).trans
    (WalkSegment.of_link hl5'), rfl⟩

/-- info: 'LeanLLVM.Refinement.WalkScope.strPath5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strPath5

/-! ### Links 6 to 8

The depth-zero value-position call, the key-zero merge and the arena
reservation, composed onto the first five.  Every fact here is the bundle's,
`WalkInv`'s, or the previous link's target — the two crossings of
`if.end207.i`'s store are the lemmas above — except for `%idxprom.i`, which no
carrier names and which is therefore read at the head and carried through the
states by the shape of their environments. -/

/-- **The head's count test, read as the counts' order.**  `%inc.i = %k.0.i249 + 1`
and `%nep` are the bundle's two casts of `C.k + 1` and `G.nep`, and the test is
`ult`, so the two-entry advance's lane is inside the stream. -/
theorem strCount_test {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (f : HstringFacts G C s) : C.k + 1 < G.nep := by
  have hk64 : C.k + 1 < 2 ^ 64 := by
    have h1 := hInv.k_le; have h2 := G.nep_le; have h3 := G.maxDoc
    simp only [stage2MaxDocument] at h3
    omega
  have hincv : (BitVec.ofNat 64 (C.k + 1)).toNat = C.k + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have h1 := G.nep_le; have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have h := (walkEvalICmp_ult_one_iff _ _).1 f.hcount
  rw [hincv, hnepv] at h
  exact h

/-- **`if.end256.i`'s `%conv211.i` is one past the entry's document extent.**  The
lane `%conv211.i` holds is the *next* entry's position, and the bundle ties that
position to `%idxprom.i`'s and the token's extent (`HstringFacts.hext`); the
stream's strict order is `strLane_lt`. -/
theorem strAdvance {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (f : HstringFacts G C s) :
    (BitVec.ofNat 64 f.q).toNat = f.ix.toNat + f.ext + 1 := by
  have hk1 := strCount_test G C s hInv f
  have hq32 : f.q < 2 ^ 32 := by
    rw [f.hq]
    have h1 := entryPos_lt G hk1
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hq64 : f.q < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64, f.hq]
  have hlt := strLane_lt G hk1
  have hext := f.hext
  have hixp := f.hixPos
  omega

/-- **Links 6 to 8 compose.**  From `if.then219.i`'s state to `if.end256.i`'s.
The value-position call's answer is the head's (`s2_value_pos` reads nothing at
depth zero, so its reply does not depend on the memory the call is made at); the
merge's key bit is the `if.then219.i` edge's `0` and its count bit the callee's
non-zero answer; and the reservation's two log words cross the cursor-record
store while its `%outn.i` zero is inside the four stack objects.  The block's own
check is clear at `walkArenaReserve_clear` and the bundle's arithmetic, so the
carry the link leaves is `strC₈`. -/
theorem strPath8 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s) :
    ∃ s', WalkSegment (stage2Calls stage2SubCalls) G C s (strC₈ C f.ix f.ext) s' 8 ∧
      s' = strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s := by
  obtain ⟨s5, hseg5, hs5⟩ := strPath5 G C s hhead hInv f
  subst hs5
  have hInv5 : WalkInv G (strC₅ C) (strS₅ G C f.q s) := hseg5.inv'
  have hk1 := strCount_test G C s hInv f
  -- ---- link 6: `if.then219.i`
  have hrootEq : f.root = G.next0 + 8 := by
    have h1 : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
      hInv.regs ⟨"%root_done.i", .ptr (G.next0 + 8)⟩ (by simp [walkStaticRegs])
    exact Value.ptr.inj (Option.some.inj (f.hroot.symm.trans h1))
  have hroot5 : lookupName (strS₅ G C f.q s).env "%root_done.i"
      = some (.ptr (G.next0 + 8)) :=
    hInv5.regs ⟨"%root_done.i", .ptr (G.next0 + 8)⟩ (by simp [walkStaticRegs])
  have hread5 : readBytes (strS₅ G C f.q s).mem (G.next0 + 8) 4
      = some (natToBytes f.rd.toNat 4) := by
    have hreadRoot : readBytes s.mem (G.next0 + 8) 4
        = some (natToBytes f.rd.toNat 4) := by
      rw [← hrootEq]; exact f.hreadRoot
    have h := walkReadBytes_rootSlot_at (G := G) (C := C) (s := s) (k := C.k + 2)
      (rd := f.rd) hreadRoot
    simpa only [strS₅, strSetK₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt] using h
  have hspv : (BitVec.ofNat 32 C.sp).toNat = 0 := by rw [f.hsp0]; decide
  have hpre5 : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 f.rd,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (strS₅ G C f.q s).mem (strS₅ G C f.q s).next :=
    ⟨BitVec.ofNat 32 C.sp, f.rd, C.stage.ctype, C.stage.cst, rfl, Or.inl hspv⟩
  have hx5 : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 f.rd,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (strS₅ G C f.q s).mem (strS₅ G C f.q s).next = some r →
      r.ret = .int 32 f.xv := by
    intro r hr
    obtain ⟨r0, hcall0, -, -⟩ := s2ValuePosContract.resolves (next := s.next) f.hpreV
    have hsame := s2ValuePosCall_ret_at_zero
      (mem := (strS₅ G C f.q s).mem) (mem' := s.mem)
      (next := (strS₅ G C f.q s).next) (next' := s.next)
      (sp := BitVec.ofNat 32 C.sp) (rd := f.rd) (ct := C.stage.ctype)
      (cs := C.stage.cst) (r := r) (r' := r0) hspv hr (by
        simpa only [strS₅, strSetK₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt]
          using hcall0)
    rw [hsame, f.hxv r0 hcall0]
  obtain ⟨s6, hl6, hs6⟩ :=
    WalkLink.if_then219_i (G := G) (C := strC₅ C) (s := strS₅ G C f.q s) hInv5 rfl
      (root := G.next0 + 8) (rd := f.rd) (x := f.xv) hroot5 hread5 hpre5 hx5
  have hbit6 : evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1 := by
    rw [f.hsp0]; decide
  have hs6' : s6 = strS₆ G C f.q f.rd f.xv s := by
    rw [hs6, hbit6, if_pos rfl]
    rfl
  subst hs6'
  have hcarry6 : ({ strC₅ C with
      block := (if evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1
        then "if.end245.i" else "land.lhs.true.i") } : WalkCarry G) = strC₆ C := by
    rw [hbit6, if_pos rfl]
  have hl6' : WalkLink (stage2Calls stage2SubCalls) G (strC₅ C) (strS₅ G C f.q s)
      (strC₆ C) (strS₆ G C f.q f.rd f.xv s) := by
    rw [← hcarry6]; exact hl6
  -- ---- link 7: `if.end245.i`
  have hInv6 : WalkInv G (strC₆ C) (strS₆ G C f.q f.rd f.xv s) := hl6'.inv'
  have hcall7 : lookupName (strS₆ G C f.q f.rd f.xv s).env "%call222.i"
      = some (.int 32 f.xv) := by
    simp [strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt, cells,
      lookupName]
  have hv7 : evalOperand (strS₆ G C f.q f.rd f.xv s)
      (.imm (.int 1 (BitVec.ofNat 1 0))) = some (.int 1 0) := rfl
  have hbit7 : (if (0 : BitVec 1) = 1 then (1 : BitVec 1)
      else evalICmp .ne f.xv (BitVec.ofNat 32 0)) = 1 := by
    rw [if_neg (by decide : ¬ ((0 : BitVec 1) = 1)), f.hbranch]
  obtain ⟨s7, hl7, hs7⟩ :=
    WalkLink.if_end245_i (G := G) (C := strC₆ C) (s := strS₆ G C f.q f.rd f.xv s)
      hInv6 rfl (p := "if.then219.i") (op := .imm (.int 1 (BitVec.ofNat 1 0)))
      (k := 0) (x := f.xv) rfl if_end245_key_then219 hv7 hcall7
  have hs7' : s7 = strS₇ G C f.q f.rd f.xv s := by
    rw [hs7, hbit7, f.hbranch, if_pos rfl]
    rfl
  subst hs7'
  have hcarry7 : ({ strC₆ C with
      block := (if (if (0 : BitVec 1) = 1 then (1 : BitVec 1)
        else evalICmp .ne f.xv (BitVec.ofNat 32 0)) = 1
        then "if.end256.i" else "if.then249.i") } : WalkCarry G) = strC₇ C := by
    rw [hbit7, if_pos rfl]
  have hl7' : WalkLink (stage2Calls stage2SubCalls) G (strC₆ C)
      (strS₆ G C f.q f.rd f.xv s) (strC₇ C) (strS₇ G C f.q f.rd f.xv s) := by
    rw [← hcarry7]; exact hl7
  -- ---- link 8: `if.end256.i`
  have hInv7 : WalkInv G (strC₇ C) (strS₇ G C f.q f.rd f.xv s) := hl7'.inv'
  have hregs7 : WalkRegs G C (strS₇ G C f.q f.rd f.xv s).env := hInv7.regs
  have hidx7 : lookupName (strS₇ G C f.q f.rd f.xv s).env "%idxprom.i"
      = some (.int 64 f.ix) := by
    simpa [strS₇, strS₆, strS₅, strSetK₅, strS₄, strS₃, strS₂, strS₁, State.bind,
      stateAt, cells, lookupName] using f.hix
  have hcv7 : lookupName (strS₇ G C f.q f.rd f.xv s).env "%conv211.i"
      = some (.int 64 (BitVec.ofNat 64 f.q)) := by
    simp [strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt, cells,
      lookupName]
  have hreadA7 : readBytes (strS₇ G C f.q f.rd f.xv s).mem (C.stage.z + 48) 8
      = some (natToBytes f.A.toNat 8) := by
    have hmem : (strS₇ G C f.q f.rd f.xv s).mem
        = writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)) := rfl
    rw [hmem, walkReadBytes_log_of_cursorK (c := C.stage.c) (z := C.stage.z)
      (off := 48) (w := 8) (k := C.k + 2) (walkCursorLog_sep C.stage) (by decide)]
    exact f.hreadA
  have houtn7 : lookupName (strS₇ G C f.q f.rd f.xv s).env "%outn.i"
      = some (.ptr (G.next0 + 20)) :=
    hregs7 ⟨"%outn.i", .ptr (G.next0 + 20)⟩ (by simp [walkStaticRegs])
  have halen7 : lookupName (strS₇ G C f.q f.rd f.xv s).env "%alen"
      = some (.ptr (C.stage.z + 48)) :=
    hregs7 ⟨"%alen", .ptr (C.stage.z + 48)⟩ (by simp [walkStaticRegs])
  have hacap7 : lookupName (strS₇ G C f.q f.rd f.xv s).env "%acap"
      = some (.ptr (C.stage.z + 56)) :=
    hregs7 ⟨"%acap", .ptr (C.stage.z + 56)⟩ (by simp [walkStaticRegs])
  have hiv8 : f.ix.toNat < G.n := by
    rw [f.hixPos]
    exact entryPos_lt G (by omega : C.k < G.nep)
  have hnext8 : (BitVec.ofNat 64 f.q).toNat = f.ix.toNat + f.ext + 1 :=
    strAdvance G C s hInv f
  have hpl8 : f.ix.toNat + f.ext ≤ G.n := by
    have h1 := entryPos_lt G (by omega : C.k + 1 < G.nep)
    have hext := f.hext
    have hixp := f.hixPos
    omega
  obtain ⟨s8, hl8, hs8⟩ :=
    WalkLink.if_end256_i (G := G) (C := strC₇ C) (s := strS₇ G C f.q f.rd f.xv s)
      hInv7 rfl (ix := f.ix) (cv := BitVec.ofNat 64 f.q) (A := f.A) (Cc := f.Cc)
      hidx7 hcv7 houtn7 halen7 hacap7 hreadA7 f.hCc (ext := f.ext) hiv8 hnext8 hpl8
      f.hcur
  -- the block's check is clear: `walkArenaReserve_clear`'s arithmetic, read at the
  -- binding the link made
  have hAle : f.A.toNat ≤ C.alen := hInv7.logArena_le hreadA7
  have hle8 : f.ext + 64 + f.A.toNat ≤ G.dstcap := by
    have hroom := G.arenaRoom
    simp only [stage2ArenaReserve] at hroom
    have hwin := f.hwin
    omega
  have hCcNat : f.Cc.toNat = G.dstcap := by
    have h := congrArg bytesToNat f.hCc
    rw [natToBytes_toNat, wordBytes, natToBytes_toNat] at h
    have h1 : f.Cc.toNat % 256 ^ 8 = f.Cc.toNat := by
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt f.Cc.isLt]
    have h2 : G.dstcap % 256 ^ 8 = G.dstcap := by
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt G.dstcapLt]
    omega
  have hbit8 : evalICmp .ugt ((BitVec.ofNat 64 f.q)
      + (f.ix ^^^ BitVec.ofNat 64 18446744073709551615)
      + BitVec.ofNat 64 64 + f.A) f.Cc = 0 := by
    have hadd : (BitVec.ofNat 64 f.q)
        + (f.ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64 + f.A
        = BitVec.ofNat 64 (f.ext + 64 + f.A.toNat) := by
      have hxor : (f.ix ^^^ BitVec.ofNat 64 18446744073709551615)
          = BitVec.ofNat 64 (2 ^ 64 - 1 - f.ix.toNat) := by
        have h := walkOfNat_xor_allOnes (w := 64) (p := f.ix.toNat) f.ix.isLt
        simpa only [walkOfNat_toNat] using h
      have hsum : f.ext + 64 + f.A.toNat < 2 ^ 64 := by
        have := G.dstcapLt; omega
      rw [hxor]
      bv_omega
    rw [hadd, ← walkOfNat_toNat f.Cc, hCcNat]
    exact walkEvalICmp_ugt_ofNat_zero (by omega) G.dstcapLt hle8
  have hnext8pc : walkIfEnd256Next f.A f.Cc (BitVec.ofNat 64 f.q) f.ix
      = "z_arena_reserve.exit" := by
    rw [walkIfEnd256Next, hbit8, if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]
  have hs8' : s8 = strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s := hs8
  subst hs8'
  have hcarry8 : ({ strC₇ C with
      block := walkIfEnd256Next f.A f.Cc (BitVec.ofNat 64 f.q) f.ix,
      pending := some (f.ix.toNat, (strC₇ C).alen, f.ext) } : WalkCarry G)
      = strC₈ C f.ix f.ext := by
    rw [hnext8pc]
  have hl8' : WalkLink (stage2Calls stage2SubCalls) G (strC₇ C)
      (strS₇ G C f.q f.rd f.xv s) (strC₈ C f.ix f.ext)
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) := by
    rw [← hcarry8]; exact hl8
  exact ⟨_, ((hseg5.trans (WalkSegment.of_link hl6')).trans
    (WalkSegment.of_link hl7')).trans (WalkSegment.of_link hl8'), rfl⟩

/-! ### Links 9 and 10

The reservation's completion and `NodeBlock31`'s edge.  The call at
`z_arena_reserve.exit` is the one place the composition cannot read its own
hypotheses: the callee's answer `r` and its memory facts are the string body's,
and the layer states no producer of that contract's staging *at the call's own
memory* — `s2StringBodyPre_at_string_call` produces the precondition, not the
answer's frame.  So the answer is a parameter, and its six memory clauses are
**one** premise (residue R1) whose producer the docstring names.  The decoded
length `%sub260.i` and the token's extent are the same number
(`walkSub260_eq`), which is what makes the link's `hsub` read off the state. -/

/-- **Links 9 and 10 compose.**  From `if.end256.i`'s state to `LeafBlock29`'s:
the reservation's completion — the callee's answer, the log's base word and the
cursor record's `%sub260.i`, all at the state the previous link left — and
`NodeBlock31`'s edge, whose `%call272.i` is the callee's answer and whose bit is
R8's.

**The parameters, and what produces each.**

* `harr` — `%arrayidx10.i` at the header's cell, `%3 + %idxprom.i` at `%3 = G.b`
  and the bundle's `%idxprom.i`; no block of the chain rebinds the register, but
  `walkStaticRegs` does not name it, so the composition carries it.  `hcreg`,
  `hxpreg` and `hnxpreg` are the same shape for `%c.i`, `%xp` and `%nxp`: `entry`
  binds them from the program's parameters, no block rebinds them, and the
  carrier omits them — which is the 39-site `WalkInv`-vocabulary change the header
  measures, not a lemma of this layer.
* `hreadAr` — residue **R5**, the log's arena-base word at `%z + 40`.  Producer:
  the initialisation's store at `%z + 40` plus a `WalkInv` clause for the
  arena's base; `WalkInv.owned` gives the object's presence only, and the clause
  set binds `+8`, `+16`, `+32`, `+48` and `+56`.
* `hGdst` — residue **R6**, the arena's staged address width.  `WalkGeom` bounds
  `dstcap`, never `dst`; producer: the ABI staging's address width
  (`stage2Regions`' `HasBytes` at `%dst`).
* `r`, `hcallR` — the callee's `CallOutcome`, which the states after link 9
  carry; its producer is the string body's contract at the staging assembled by
  `s2StringBodyPre_at_string_call`.
* `hretR` — the answer's word, `%call272.i`.  Producer: `s2StringBodyPost`'s
  `form` at that call (`s2StringBody_sound`), which is the bundle's `y` on the
  accepting arm.
* `hbodyR` — residue **R1**: the six memory clauses, one premise.  Producer:
  `s2StringBodyFoot_frame_walkWide` for the frame and the four crossings
  (`readBytes_of_frame` at the log and the event stream,
  `WalkStackBytes.write_outside` at the two stacks).
* `hR8` — residue **R8**, `NodeBlock31`'s edge.  Producer: the callee's post —
  the form is `1` or `2` on the accepting arms, and neither is `< 1` signed;
  its `form ≠ 0` is also what the write-back's `l ≤ ext` producer needs. -/
theorem strPath10 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s)
    (harr : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%arrayidx10.i"
      = some (.ptr (G.b + f.ix.toNat)))
    (hcreg : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%c.i"
      = some (.ptr C.stage.c))
    (hxpreg : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%xp"
      = some (.ptr G.xp))
    (hnxpreg : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%nxp"
      = some (.int 64 (BitVec.ofNat 64 G.nxp)))
    (hreadAr : readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (C.stage.z + 40) 8 = some (wordBytes 8 G.dst))
    (hGdst : G.dst < 2 ^ 64)
    (r : CallOutcome)
    (hcallR : stage2Calls stage2SubCalls "s2_string_body"
      [.ptr C.stage.c, .ptr (G.b + f.ix.toNat + 1), .int 64 (BitVec.ofNat 64 f.ext),
        .ptr (G.dst + f.A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
        .int 64 (BitVec.ofNat 64 G.nxp)]
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next = some r)
    (hretR : r.ret = .int 32 f.y)
    (hbodyR :
      UnchangedOutside m0 r.mem (walkWide G (strC₉ C f.ix f.ext)) ∧
      (∀ x ∈ walkStaged G (strC₉ C f.ix f.ext), HasBytes r.mem x.1 x.2) ∧
      (∀ off w, off + w ≤ stage2LogExtent →
        readBytes r.mem (C.stage.z + off) w =
          readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
            (C.stage.z + off) w) ∧
      (readBytes r.mem (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length =
        readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length) ∧
      WalkStackBytes r.mem C.stage.ctype C.tyMap C.wlen ∧
      WalkStackBytes r.mem C.stage.cst C.stMap C.wlen)
    (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0) :
    ∃ s', WalkSegment (stage2Calls stage2SubCalls) G C s (strC₁₀ C f.ix f.ext) s' 10 ∧
      s' = strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s := by
  obtain ⟨s8, hseg8, hs8⟩ := strPath8 G C s hhead hInv f
  subst hs8
  have hInv8 : WalkInv G (strC₈ C f.ix f.ext)
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) := hseg8.inv'
  have hregs8 : WalkRegs G C (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env :=
    hInv8.regs
  obtain ⟨hframeR, hownedR, hlogR, hevR, hstTyR, hstStR⟩ := hbodyR
  -- ---- link 9: `z_arena_reserve.exit`
  have hpend8 : (strC₈ C f.ix f.ext).pending = some (f.ix.toNat, C.alen, f.ext) := rfl
  have hz36 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%z.val36"
      = some (.int 64 f.A) := by
    simp [strS₈, walkIfEnd256OutAt, stateAt, cells, lookupName]
  have hreadA8 : readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (C.stage.z + 48) 8 = some (natToBytes f.A.toNat 8) := by
    have hmem : (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
        = writeBytes
            (writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)))
            (G.next0 + 20) (natToBytes (BitVec.ofNat 64 0).toNat 8) := rfl
    rw [hmem, walkReadBytes_writeBytes_outside (start := G.next0 + 20)
      (addr := C.stage.z + 48) (n := 8)
      (v := natToBytes (BitVec.ofNat 64 0).toNat 8) ?_]
    · rw [walkReadBytes_log_of_cursorK (c := C.stage.c) (z := C.stage.z) (off := 48)
        (w := 8) (k := C.k + 2) (walkCursorLog_sep C.stage) (by decide)]
      exact f.hreadA
    · left
      have hz := C.stage.sevenEnd (C.stage.z, stage2LogExtent)
        (by simp [stage2StagedWrites])
      simp only [stage2LogExtent] at hz
      omega
  have hAle8 : f.A.toNat ≤ C.alen := hInv8.logArena_le hreadA8
  have hpos : (f.A.signExtend 64).toNat < 2 ^ 63 := by
    have h1 : f.A.toNat < 2 ^ 63 := by
      have h2 := f.hwin
      have h3 := G.maxDoc
      simp only [stage2MaxDocument] at h3
      omega
    simpa using h1
  have hsub8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%sub260.i"
      = some (.int 64 (BitVec.ofNat 64 f.ext)) := by
    have hval : (BitVec.ofNat 64 f.q)
        + (f.ix ^^^ BitVec.ofNat 64 18446744073709551615)
        = BitVec.ofNat 64 f.ext :=
      walkSub260_eq (strAdvance G C s hInv f)
    simp [strS₈, walkIfEnd256OutAt, stateAt, cells, lookupName, hval]
  have har8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%ar"
      = some (.ptr (C.stage.z + 40)) :=
    hregs8 ⟨"%ar", .ptr (C.stage.z + 40)⟩ (by simp [walkStaticRegs])
  have hc8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%c.i"
      = some (.ptr C.stage.c) := hcreg
  have houtn8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%outn.i"
      = some (.ptr (G.next0 + 20)) :=
    hregs8 ⟨"%outn.i", .ptr (G.next0 + 20)⟩ (by simp [walkStaticRegs])
  have hxp8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%xp"
      = some (.ptr G.xp) := hxpreg
  have hxj8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%xj.i"
      = some (.ptr (G.next0 + 12)) :=
    hregs8 ⟨"%xj.i", .ptr (G.next0 + 12)⟩ (by simp [walkStaticRegs])
  have hnxp8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%nxp"
      = some (.int 64 (BitVec.ofNat 64 G.nxp)) := hnxpreg
  obtain ⟨s9, hl9, hs9⟩ :=
    WalkLink.z_arena_reserve_exit (G := G) (C := strC₈ C f.ix f.ext)
      (s := strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) hInv8 rfl
      (p := f.ix.toNat) (off := C.alen) (ext := f.ext) hpend8 (A := f.A)
      hz36 hpos hreadA8 har8 hGdst hreadAr harr hsub8 hc8 houtn8 hxp8 hxj8 hnxp8
      f.hwin (r := r) hcallR hframeR hownedR hlogR hevR hstTyR hstStR
  have hs9' : s9 = strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s := hs9
  subst hs9'
  have hl9' : WalkLink (stage2Calls stage2SubCalls) G (strC₈ C f.ix f.ext)
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) (strC₉ C f.ix f.ext)
      (strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := by
    simpa only [strC₉] using hl9
  -- ---- link 10: `NodeBlock31`
  have hInv9 : WalkInv G (strC₉ C f.ix f.ext)
      (strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := hl9'.inv'
  have h1_10 : evalOperand (strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)
      (.reg "%call272.i") = some (.int 32 f.y) := by
    simp [strS₉, walkZArenaReserveExitOutAt, stateAt, evalOperand, lookupName, hretR]
  obtain ⟨s10, hl10, hs10⟩ :=
    WalkLink.NodeBlock31_at (calls := stage2Calls stage2SubCalls) (G := G)
      (C := strC₉ C f.ix f.ext) (s := strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)
      hInv9 rfl (x1 := f.y) h1_10
  have hs10' : s10 = strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s := by
    rw [hs10, hR8, if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]
    rfl
  subst hs10'
  have hleaf : (if evalICmp .slt f.y (BitVec.ofNat 32 1) = 1
      then "cleanup339.critedge.i" else "LeafBlock29") = "LeafBlock29" := by
    rw [hR8, if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]
  have hl10' : WalkLink (stage2Calls stage2SubCalls) G (strC₉ C f.ix f.ext)
      (strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) (strC₁₀ C f.ix f.ext)
      (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := by
    rw [hleaf] at hl10
    simpa only [strC₁₀] using hl10
  exact ⟨_, (hseg8.trans (WalkSegment.of_link hl9')).trans
    (WalkSegment.of_link hl10'), rfl⟩

/-! ### Axiom footprints

Each pin states the footprint the lemma actually has.  The segment's projection
and the arm cost `propext` and `Quot.sound` — no `Classical.choice`: nothing here
selects from a disjunction or a `gep`, which is what carries choice elsewhere in
the layer. -/

/-- info: 'LeanLLVM.Refinement.WalkScope.stringPath_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stringPath_seg

/--
info: 'LeanLLVM.Refinement.WalkScope.WalkDispatchResult.ofStringMerge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms WalkDispatchResult.ofStringMerge

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEvalICmp_ult_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkEvalICmp_ult_one_iff

/-- info: 'LeanLLVM.Refinement.WalkScope.strPath8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strPath8

/-- info: 'LeanLLVM.Refinement.WalkScope.strPath10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strPath10

end WalkScope

end LeanLLVM.Refinement
