/-
The two-entry token: the standalone string's bundle and its `merge` arm.

## What this bundle is

`HstringFacts` is the input's facts at a head state whose token consumes **two**
entries — a standalone string's opener and its closer — grouped by subject, and
`WalkDispatchResult.ofStringMerge` is the `merge` arm those facts support, proved
from them and from the path's residue (`HstringResidue`): the
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

### The segment is proved, and the residue is its parameters

**The arm is produced, and so is its segment.**  `WalkDispatchResult.ofStringMerge`
is a theorem from the bundle and the residue — the `merge` arm, its index, its
depth, its two bounds and its price are all read from the segment's endpoint and
from the invariant there — and the segment itself is `stringPath_seg`'s
conclusion, composed from the fifteen links.  `WalkDispatchResult.toOutcome` still
decides `cont`/`finish` from the merge's own test on the index the segment reached.

**The fifteen links, and where each is composed.**  `strPath5` composes links 1–5
(the four class-A branches and the two-entry advance), `strPath8` links 6–8 (the
value-position call, the key-zero merge and the arena reservation), `strPath9`
link 9 (the string body's call), `strPath10` link 10 (`NodeBlock31`'s edge), and
`stringPath_seg` links 11–15 (the answer's own test, its two arms, the arena merge
and the record, and the container's advance).  Every intermediate state is a `def`
(`strS₁`–`strS₁₅`), every carry is the named `strC₁`–`strC₁₅`, and each link's
target is its own `def`, byte for byte — which is why the casts are the links and
the header's table is the composition.

**The states had to become nameable, and they are.**  A composition threads each
link's *target* state into the next link's hypotheses, so no link may conclude
`∃ s', WalkLink … s'` without saying which state `s'` is.  `NodeBlock21_at`,
`NodeBlock5_at`, `LeafBlock_at`, `sw_bb202_i_at`, `NodeBlock31_at`,
`LeafBlock29_at` and `if_else285_i_at` always did; `if_then281_i`, `if_end207_i`,
`if_end245_i`, `if_end290_i` and `if_then219_i` were given the equality;
`if_end256_i` and `z_arena_reserve_exit` name their targets through
`walkIfEnd256OutAt`/`walkZArenaReserveExitOutAt` (the second taking the callee's
`CallOutcome`); and `if.else334.i`'s `callQuiet` existential is exposed as
`WalkLink.if_else334_i_at`, which takes the helper's answer as a parameter and
concludes the target state.

**The residue is empty, and the rest is derived.**  With the states
nameable, every link's hypotheses are the head bundle's fields, `WalkInv`'s
clauses, the step's own predecessor, or a `def`'d state's cells.  The structure
carried thirteen fields at its first statement; eleven retired as the layers below
produced them, and the last two — the log's base and arena-base words — are
`WalkInv` clauses (`log_base`, `log_dst`), so `stringPath_seg` reads them off the
head invariant:

| id | field | statement | became |
|---|---|---|---|
| R5 | arena-base word | `readBytes s.mem (z + 40) 8 = some (wordBytes 8 G.dst)` | `WalkInv.log_dst` |
| R3 | base word | `readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)` | `WalkInv.log_base` |

The eleven retired before them, with where each is produced:

* **`r` and `hcallR`** — `s2StringBody_answers` at the transported precondition,
  inside `strPath9`;
* **R1's answer word (`hretR`)** — `stage2StringBody_head_form`
  (`JsonStage2StringStageFacts`, on `stage2StringBody_form_congr`): the model's form
  is a function of the five words it reads, and `s2StringBodyPre_of_reads` already
  spends exactly those five agreements between the head's memory and link 8's, so
  the form the model takes at the call is the form the head bundle's `hy` names as
  `y`.  The answer's word is then read off the post at the callee's own memory;
* **R8 (`hR8`)** — the arm's selector, and it lives beside the arm: a refusing
  answer is legal at this call and takes `NodeBlock31` to `cleanup339.critedge.i`
  (`if.then`, the error exit) rather than to the merge, so the accepting hypothesis
  is `HcontArm.twoEntry`'s field, not a fact about the head state;
* **`l`, `hreadOutn` and `hlext`** — `s2StringBody_outn_le` at the callee's model
  memory, plus `s2StringBody_outn_at_call` (new, in `JsonStage2StringStageFacts`)
  to carry the word across the private slot's write at the call's `next`: the pre
  separates the slot from `%outn.i`, so the length and its bound are the call's.
  `strPath9` returns them with the answer;
* **the log's base word at the answer's memory** — `strPath9` carries the head's
  word across link 8's two stores (`walkReadBytes_two_writes`, `hInv.log_base`) and
  the callee's log-silence (`s2StringBodyFrame_facts`), so the five links read it
  at `r.mem` without a premise about the callee;
* **`G.dst < 2^64`, `G.ev < 2^64` and `C.evlen < 2^63`** — `WalkGeom.dstLt`,
  `WalkGeom.evLt` and `WalkGeom.ev63` (`stage2Pre`'s clauses), the last through
  `WalkInv.evlen_le`.

**The event count is derived, not supplied.**  `WalkInv.events_le` states
`C.events.length ≤ C.k + walkEmitC C.block`, whose allowance is zero at every block
before the current entry's append — the loop head among them — so
`WalkInv.events_le_of_tight` gives `C.events.length ≤ C.k` there, and the head's
guard gives `C.k < G.nep`.  Those are exactly the two hypotheses `if.then328.i`
takes: the tight count is what the emit must re-establish at its target (the carry's
`k` does not advance until the merge) and the head's guard is the entry the record
accounts for.  The residue carried the strict form `length < C.k`, which is
uninhabited at a one-entry document's last entry (`C.k = 0`), and it is now gone
with the clause it was reading.

**The body's six memory clauses are produced, not supplied.**  `strPath9` derives
them from the head bundle in four steps, all of which are lemmas of
`JsonStage2StringStageFacts` now:

* **the precondition's transport to the call's memory.**
  `s2StringBodyPre_of_reads` moves the whole precondition across the two stores
  link 8 makes — `%c.i + 32` (`if.end207.i`'s `%k` word) and `%outn.i`'s zero
  (`if.end256.i`) — given agreement at the five reads it names
  (`stage2ReadWord` at `%c.i`, at `%c.i + 1112` and at `%xj.i`, `readLanes32` at
  `%xp`, `readBytes` at the body's window) and presence monotonicity.  Each
  agreement is `walkReadBytes_two_writes`, which needs only the regions'
  separation: the document's and the escape list's from the cursor record
  (`walkWrites_against_abi`), and every staged object's from the cursor's
  interval (`WalkStage.sevenEnd`, `WalkGeom.watermark`).  The bundle's `hpreS` is
  the input, and `s2StringBody_sound` at the transported precondition is the
  callee's answer (R1's `hpost`);
* **the accepting arm's form.**  R8's word is not zero, so the model's form is not
  zero (`hform0`), which is the hypothesis the arm's frame needs;
* **the four write entries.**  `s2StringBody_frame_of_form` gives the frame over
  the four entries an accepting arm writes, and
  `s2StringBodyFrame_walkWideAt` widens it to the run's `walkWideAt` at the carry
  and cursor the call leaves;
* **the four crossings.**  `s2StringBodyFrame_facts` reads the log's and the
  trace's read equalities out of that silence (`readBytes_of_frame`), carries the
  presence over `walkStaged` by monotonicity, and transports the two stack maps —
  the silence is the *callee's* four entries, not the run's list, because
  `walkWideAt` contains the log and the stream as entries and a frame over it says
  nothing about either;
* **the frame's composition.**  The run's own silence is `WalkInv.frame` extended
  by the two stores (`UnchangedOutside.write_inside`), grown to the call's carry
  and cursor (`walkWideAt_grow`), and composed with the callee's frame
  (`UnchangedOutside.trans'`).

That is why `HstringResidue` no longer has a memory field: what was owed there was
a lemma, and the lemma is the composition above, not a premise.

**What the arm reads.**  `WalkDispatchResult.ofStringMerge` reads the segment,
its endpoint's block, index and predecessor, the endpoint's two cells and G2's
count test (`hcount`, without which there is no `k2 ≤ nepv.toNat` for the merge's
`hcap`).  The other groups are the premise set the composition consumes, which is
why the bundle keeps them.

**The cursor pin is landed.**  `next_ge : G.next0 + stage2BootstrapExtent ≤
s.next` (`stage2BootstrapExtent := 28`, the end of `entry`'s four `alloca`s) is a
`WalkInv` clause, and the frame is the cursor's interval
(`walkPresent G C ++ [(G.next0, s.next - G.next0)]`).  The clause is preserved by
every dispatch step and produced at the seed; the composition below reads it at the
call's state, which is what makes the callee's private slot inside the interval.

**Why `WalkSegment` is not a bundle field.**  A field that *is* the merge arm's
segment would make the bundle a restatement of the arm it produces, so the bundle
would be green whenever the arm is and say nothing.  The segment is a *theorem*
now (`stringPath_seg`), and the residue is what it is a theorem *from*.

The link's `%xj.i` is the staging's address, `G.next0 + 12`; an earlier statement
of it had `+ 16`, where `s2StringBodyPre`'s `RegionsApart xj 8 outn 8` fails
against `%outn.i = G.next0 + 20`, so that earlier statement was uninhabited and
the census row that called the link proved records a proof, not an inhabitant.
The repair is at the link, and the composition uses the repaired statement.

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
| G8 | the verdict and the record | **supplied**: the callee's return word; **produced** by the invariant for `%7` (`iter.reg7`) and the two log words (`log_len`, `log_cap`).  The decoded length the body wrote at `%outn.i` is **not** a field: no block of the walk reads the slot at a head, and the write-back that does (`if.else285.i`) reads the callee's answer, which `strPath9` derives at the call |
| G9 | the merge's two cells | **proved** by `stringPath_seg`, which reads them off the endpoint state the segment reaches: `WalkSegment` records a run and an invariant, not the blocks it passed, so no lemma carries `%inc208.i` from `if.end207.i` to the merge across a *supplied* segment — and the composition reads it because the state is a `def` |

Two of the supplied groups are supplied for a reason that is not a missing
lemma but a vocabulary gap, and the header keeps them distinct: G4/G7's call
preconditions are the helper contracts' own staging, which is what a producer of
`s2ValuePosPre`/`s2StringBodyPre` supplies, and `%arrayidx10.i` is the register the
header rebinds every iteration, so no static carrier can name it.  Nothing above
is weakened to make a proof go through: every field is either the invariant's
clause read at `s`, a property of the document, or a named supplied premise.

**Why the fields are stated at the head.** G1–G8's fields are stated at the head state `s` (and at `s.mem`/`s.next` for the
memory and the allocator cursor), which is where they are true of the run: the
intervening blocks read those cells rather than rebind them (`%8`, `%inc.i`,
`%nep`, `%4`, `%root_done.i`, `%idxprom.i`, `%7`, the log's words), and the
run's writes are separated from the log's cursor slot and the document.

**The reconciliation to each consuming link's own state is the composition's, not
the bundle's.**  `WalkSegment` (`JsonStage2WalkTraverse`) is a
`run : ∀ n, runFuel … = runFuel …` and an `inv' : WalkInv G C' s'` — no memory, no
allocator cursor, no intermediate state.  So `hpreS` (the string body's
precondition at `s.mem`/`s.next`), `hreadA` (the log's arena word) and the
log's two words are statements about the **head's** memory, and each is
transported to the block that reads it by the composition: the cursor's advance
runs through `strPath8`, the record's store at `%z.val` and the log's two words
are read off the invariant at the state that reads them (`log_len`, `log_cap`),
and the two calls' memories and allocator cursors are the `def`'d states'
`mem`/`next`.  That transport is why the group's sources are named individually,
and stating the fields at the head is what keeps it visible.

-/

import LeanLLVM.Refinement.JsonStage2WalkCall
import LeanLLVM.Refinement.JsonStage2WalkPhi
import LeanLLVM.Refinement.JsonStage2WalkSteps
import LeanLLVM.Refinement.JsonStage2WalkStore
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun
import LeanLLVM.Refinement.JsonStage2WalkRevolution
import LeanLLVM.Refinement.JsonStage2StringStageFacts

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

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

The bundle carries no segment: `stringPath_seg` is a theorem from these fields and
the path's residue (`HstringResidue`), whose own docstrings name each field's
producer.  What the bundle states is the *input's* facts at the head, which is what
a producer of the class supplies. -/
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
  argument list is stated in the tree.  The block's *edge* is the depth's:
  `if.end245.i` at depth zero and `land.lhs.true.i` above it.  That split is not a
  fact about the token's class — both edges are the same token's — so it is a
  parameter of the theorems that read it (`strPath8`'s `hsp0`) rather than a field
  here. -/
  root : Nat
  hroot : lookupName s.env "%root_done.i" = some (.ptr root)
  rd : BitVec 32
  hreadRoot : readBytes s.mem root 4 = some (natToBytes rd.toNat 4)
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
  arm's `%add283.i` reads it), and the log's `%len`/`%cap` words are what
  `if.end290.i` tests thirteen bytes against.  The answer and the two words'
  *values* are supplied; `%7` and the two log words are the invariant's clauses
  read at the head.

  The decoded length the body wrote at `%outn.i` is **not** here.  The slot is
  read once in the body, at `if.else285.i`, and the word that load receives is
  the callee's answer: `strPath9` derives it at the call
  (`s2StringBody_outn_le` with `s2StringBodyPre_next_outn`) and the segment
  carries it to the merge.  No head state's bytes enter it, so a field stating
  them would be a carried fact with no reader. -/
  y : BitVec 32
  hy : ∀ r, stage2Calls stage2SubCalls "s2_string_body"
    [.ptr C.stage.c, .ptr (G.b + ix.toNat + 1), .int 64 (BitVec.ofNat 64 ext),
     .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
     .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r →
    r.ret = .int 32 y
  h7 : lookupName s.env "%7" = some (.int 32 (BitVec.ofNat 32 (entryPos G C.k)))
  hnl : readBytes s.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen)
  hnc : readBytes s.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)

/-! ### The continuing branch's three cases

`walkLoopStep_of_staging`'s continuing branch needs the bundle that describes the
state.  There are three: the whitespace token's (`HcontFacts`, indexed at `C.k + 1`),
the scan-free token's (`HcontCleanupFacts`, also at `C.k + 1`), and the two-entry
token's (`HstringFacts`, at `C.k + 2`).  This is their disjunction, so the `rcases` at
the call site is one line and the classification stays the merge's. -/

/-- **The continuing branch's bundle is one of the three tokens'.**  The one-entry
cases are the whitespace scan's (`HcontFacts`) and the scan-free continuation's
(`HcontCleanupFacts`, whose token ends at the entry's end so the extra-token scan is
empty); the two-entry case is the standalone string's, whose merge index overshoots the
head's test.  Every arm produced a `WalkDispatchResult` — the first through the whitespace
composition (since retired with that route), the second through `walkRevolutionMergeSeg`,
the third through `WalkDispatchResult.ofStringMerge` — so the case is named here rather than
decided by the head's index.  `HcontCase` is the *superseded* statement's type, not a live
dispatch: `JsonStage2WalkHcontDomain` uses it as the premise its regression refutes.

**The arms are disjoint at a state**, which is what makes this a class rather than a
fan-out: `HcontFacts.hlt91` says the head's byte is *not* below `91`, and
`HstringFacts.heq34` says it *is* `34`; no state satisfies both.  The two one-entry arms
are separated by the byte before the entry's end: `HcontFacts` carries that byte's class
and the skip's run is derived from it (`contWsRunF`, whose seam stores the run's stop
`k < v.toNat`), while `HcontCleanupFacts`
carries that byte's three *no-whitespace* pivots, so the seam stores the entry's end and
`heicd`'s reading of that class is `v.toNat < v.toNat` — refuted.  A producer that reads
the document's byte at `%cond350.i - 1` answers with one arm, and the consumer's branches
never overlap.

**This is a sub-union of the continuing premise, not the premise.**  The continuing
branch's evidence is `HcontArm` (`JsonStage2WalkDispatchHcontArms`), whose census
(`HcontClass.complete`) also has the plain-value numeral route and the container and
delimiter arms; `HcontCase` names only the three token bundles, and
`JsonStage2WalkHcontDomain` uses it as the *superseded* statement its regression refutes at
the document `"01"`. -/
inductive HcontCase {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type
  /-- The whitespace token: the skip runs to `k`, the token ends inside its entry, and the
  extra-token scan runs `[k, %cond350.i)`.  `HcontFacts` at the head state. -/
  | ws : HcontFacts G C s → HcontCase G C s
  /-- The scan-free continuation: the token ends at the entry's end, so `if.then447.i`'s
  target tests `ult v v` and the walk reaches `if.end473.i` without a scan.
  `HcontCleanupFacts` at the head state. -/
  | cleanup : HcontCleanupFacts G C s → HcontCase G C s
  /-- The token is a standalone string: two entries consumed, merge index
  `C.k + 2`, and `HstringFacts` at the head state. -/
  | twoEntry : HstringFacts G C s → HcontCase G C s

/-! ### The fifteen links, composed

This section is the composition of the fifteen links — links 1–10 in the three
`strPath` theorems below, links 11–15 in `stringPath_seg` at its end.  The links are
the module header's table; what a composition owes beside them is the *states* they
reach — a link's target state must be nameable before the next link's hypotheses can
be stated at it — and the handful of facts no clause of `WalkInv` carries at the
state that reads them, which is `HstringResidue`.

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

/-- **The state `if.then219.i` reaches.**  The depth is zero (`strPath8`'s `hsp0`), so
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

/-- **Two listed regions are separated in the list's order.**  `DisjointRegions` is a
`Pairwise` fact, so an entry of the left block is separated from an entry of the
right block without either pair having to be shown distinct.  This is the form the
staging's two ABI objects need: `%dst`'s window and the event stream are both
`stage2Regions` entries, and their separation is the list's order. -/
theorem DisjointRegions.left_of_right {rs ms : List (Nat × Nat)}
    (h : DisjointRegions (rs ++ ms)) {p q : Nat × Nat} (hp : p ∈ rs)
    (hq : q ∈ ms) : p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨-, -, hcross⟩ := h
  exact hcross p hp q hq

/-- **The lane reader through a store it misses.**  `readLanes32` groups four
bytes per lane, so a store outside the whole lane range leaves it alone.  The
region form of `readLanes32_congr_bytes`, beside `walkReadBytes_writeBytes_outside`. -/
theorem walkReadLanes32_writeBytes_outside {m : Mem} {start : Nat} {v : List UInt8}
    {addr k : Nat} (h : addr + 4 * k ≤ start ∨ start + v.length ≤ addr) :
    readLanes32 (writeBytes m start v) addr k = readLanes32 m addr k := by
  refine JsonEntrySteps.readLanes32_congr_bytes (fun j _hj => ?_)
  exact readByte_writeBytes_outside m v (by rcases h with h | h <;> omega)

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
    exact LeanLLVM.evalOperand_reg_of f.hinc
  have hnep₄ : evalOperand (strS₃ s) (.reg "%nep") =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    simp only [strS₃, strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%nep") _ _ (by decide)]
    exact LeanLLVM.evalOperand_reg_of f.hnep
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
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s)
    (hsp0 : C.sp = 0) :
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
  have hspv : (BitVec.ofNat 32 C.sp).toNat = 0 := by rw [hsp0]; decide
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
    rw [hsp0]; decide
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
`z_arena_reserve.exit` is the string body's, so its answer `r` is a parameter;
its six memory clauses are not a premise but the composition `strPath9` proves
below.  Their producer's two
halves are in `JsonStage2StringStageFacts` — the accepting arm's frame
(`s2StringBody_frame_of_form`) and the cursor widening
(`s2StringBodyFoot_frame_walkWideAt`) — and the transports are the
precondition's move to the memory the call is made at plus the four crossings
at that frame.  The decoded
length `%sub260.i` and the token's extent are the same number
(`walkSub260_eq`), which is what makes the link's `hsub` read off the state. -/

-- A measured ceiling, not an inherited one.  The five read transports that carry
-- the callee's precondition across link 8's two stores exceed the default budget:
-- this declaration times out at `whnf` at 200 000, 300 000 and 315 000
-- heartbeats, and at the last of those the counter trips inside `heA`'s transport,
-- the record's error word at `C.stage.c + 1112`.  The transports are separately
-- cheap and their cost is cumulative — which is why none of them is the term to
-- restate — but they sum past the budget, so the declaration keeps a raise.
-- 325 000 heartbeats suffice; the option keeps 400 000 for headroom.  The
-- composition boundaries around the work are already declarations of their own
-- (`strPath8` before, `strPath10` after), and the state and register facts ahead
-- of the transports do fit the default, so a further split would leave the
-- remaining ladder at the default's edge rather than under it.
set_option maxHeartbeats 400000 in
/-- **Links 1 to 9 compose.**  `strPath8`'s eight links, then the string body's
call at `z_arena_reserve.exit`: the callee's answer, the log's base word and the
cursor record's `%sub260.i`, all at the state the previous link left.  The
endpoint is named (`strS₉`), so `strPath10` reads the invariant there and takes
`NodeBlock31`'s edge on its own.

**The parameters, and what produces each.**

* `harr` — `%arrayidx10.i` at the header's cell, `%3 + %idxprom.i` at `%3 = G.b`
  and the bundle's `%idxprom.i`.  It is not a residue field: `WalkInv.iter.regarr`
  carries the head's cell and `strArr_of_iter` reads it at the state link 8
  leaves, so the composition supplies this parameter from the invariant.
  `%c.i`, `%xp` and `%nxp` are not parameters here either:
  they are entry parameters, `walkStaticRegs` names them, and `hInv8.regs` reads
  all three at the state link 8 leaves.
* `hreadAr` — the log's arena-base word at `%z + 40`, read at the **head** state's
  memory.  It *is* `WalkInv.log_dst`, so `stringPath_seg` supplies it from the head
  invariant, and this theorem carries it across link 8's two stores to the call's
  memory (`hreadAr8` below).
* `hR8` — the arm's selector, `NodeBlock31`'s edge, and not a residue field: the
  callee's post admits a refusing answer, and a refusing answer leaves the block at
  `cleanup339.critedge.i`, so the accepting hypothesis belongs to
  `HcontArm.twoEntry`.  Its `form ≠ 0` is also what the write-back's `l ≤ ext`
  producer needs.
* `hlogBase` — the log's base word at the head state's memory, which *is*
  `WalkInv.log_base`.  `strPath9` carries it to the answer's memory, which is where
  the five links read it.

**What this theorem produces, and why it is not a parameter.**  The callee's
answer `r` and its call are `s2StringBody_answers` at the transported
precondition; its word is `stage2StringBody_form_congr`'s — the bundle's `hy` names
the head model's form and the congruence carries it to link 8's memory, so the
post's word at the callee's memory is the bundle's `y`; the decoded length `l`, its
read at `%outn.i` and its bound are `s2StringBody_outn_le` with
`s2StringBody_outn_at_call`, which moves the word across the private slot's write;
and the log's base word at the answer's memory is the head's through link 8's two
stores and the callee's log-silence.  All five leave this theorem in its
conclusion, so `strPath10` and `stringPath_seg` read them from one place.

**The six memory clauses are not parameters.**  They are the composition the
residue used to carry as one field: the transported precondition
(`s2StringBodyPre_of_reads` over link 8's two stores), the callee's answer
(`s2StringBody_sound`), the accepting arm's four-entry frame
(`s2StringBody_frame_of_form`), the crossings (`s2StringBodyFrame_facts`), the
walk's own frame across the two stores and its growth (`write_inside`,
`walkWideAt_grow`), and the frame's composition (`trans'`).  The argument is in the
module header; the proof below is `R1's memory, produced`. -/
theorem strPath9 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s)
    (hsp0 : C.sp = 0)
    (harr : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%arrayidx10.i"
      = some (.ptr (G.b + f.ix.toNat)))
    (hreadAr : readBytes s.mem (C.stage.z + 40) 8 = some (wordBytes 8 G.dst))
    (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0)
    (hlogBase : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)) :
    ∃ (r : CallOutcome) (s' : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s (strC₉ C f.ix f.ext) s' 9 ∧
      s' = strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s ∧
      r.ret = .int 32 f.y ∧
      readBytes r.mem C.stage.z 8 = some (wordBytes 8 G.ev) ∧
      (∃ l, readBytes r.mem (G.next0 + 20) 8 = some (wordBytes 8 l) ∧ l ≤ f.ext) := by
  obtain ⟨s8, hseg8, hs8⟩ := strPath8 G C s hhead hInv f hsp0
  subst hs8
  have hInv8 : WalkInv G (strC₈ C f.ix f.ext)
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) := hseg8.inv'
  have hregs8 : WalkRegs G C (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env :=
    hInv8.regs
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
      = some (.ptr C.stage.c) :=
    hregs8 ⟨"%c.i", .ptr C.stage.c⟩ (by simp [walkStaticRegs])
  have houtn8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%outn.i"
      = some (.ptr (G.next0 + 20)) :=
    hregs8 ⟨"%outn.i", .ptr (G.next0 + 20)⟩ (by simp [walkStaticRegs])
  have hxp8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%xp"
      = some (.ptr G.xp) :=
    hregs8 ⟨"%xp", .ptr G.xp⟩ (by simp [walkStaticRegs])
  have hxj8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%xj.i"
      = some (.ptr (G.next0 + 12)) :=
    hregs8 ⟨"%xj.i", .ptr (G.next0 + 12)⟩ (by simp [walkStaticRegs])
  have hnxp8 : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%nxp"
      = some (.int 64 (BitVec.ofNat 64 G.nxp)) :=
    hregs8 ⟨"%nxp", .int 64 (BitVec.ofNat 64 G.nxp)⟩ (by simp [walkStaticRegs])
  -- ---- R1's memory, produced: the callee's answer and the four crossings
  --
  -- Link 8 writes twice — the cursor record's `%k` word at `%c.i + 32`
  -- (`if.end207.i`) and `%outn.i`'s zero (`if.end256.i`).
  have hmem8 : (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      = writeBytes
          (writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)))
          (G.next0 + 20) (natToBytes (BitVec.ofNat 64 0).toNat 8) := rfl
  have hlen8 : (wordBytes 8 (C.k + 2)).length = 8 := by
    simp [wordBytes, natToBytes_length]
  have hzero8 : (natToBytes (BitVec.ofNat 64 0).toNat 8).length = 8 :=
    natToBytes_length _ 8
  -- link 8's two stores are both outside the log object, so every word of it reads
  -- the same at the call's memory as at the head's
  have hlogRead : ∀ off, off + 8 ≤ stage2LogExtent →
      readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem (C.stage.z + off) 8
        = readBytes s.mem (C.stage.z + off) 8 := by
    intro off hoff
    rw [hmem8, walkReadBytes_writeBytes_outside (start := G.next0 + 20)
      (addr := C.stage.z + off) (n := 8)
      (v := natToBytes (BitVec.ofNat 64 0).toNat 8) ?_]
    · rw [walkReadBytes_log_of_cursorK (c := C.stage.c) (z := C.stage.z) (off := off)
        (w := 8) (k := C.k + 2) (walkCursorLog_sep C.stage) hoff]
    · left
      have hz := C.stage.sevenEnd (C.stage.z, stage2LogExtent)
        (by simp [stage2StagedWrites])
      simp only [stage2LogExtent] at hz hoff
      omega
  have hreadAr8 : readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (C.stage.z + 40) 8 = some (wordBytes 8 G.dst) :=
    (hlogRead 40 (by decide)).trans hreadAr
  have hwC8 : C.stage.c + 1192 ≤ G.next0 := by
    have h := C.stage.sevenEnd (C.stage.c, stage2CursorExtent)
      (by simp [stage2StagedWrites])
    simpa only [stage2CursorExtent] using h
  have hwDoc8 : G.b + (G.n + 32) ≤ G.next0 := by
    have h := G.watermark (G.b, G.n + stage2ReadTail) (by simp [stage2Regions])
    simpa only [stage2ReadTail] using h
  have hwXp8 : G.xp + 4 * G.nxp ≤ G.next0 :=
    G.watermark (G.xp, 4 * G.nxp) (by simp [stage2Regions])
  have hdocC : C.stage.c + 1192 ≤ G.b ∨ G.b + (G.n + 32) ≤ C.stage.c := by
    have h := walkWrites_against_abi C.stage (a := G.b) (n := G.n + stage2ReadTail)
      (by simp [stage2Regions]) (C.stage.c, stage2CursorExtent)
      (by simp [stage2StagedWrites])
    simpa only [stage2CursorExtent, stage2ReadTail] using h
  have hxpC : C.stage.c + 1192 ≤ G.xp ∨ G.xp + 4 * G.nxp ≤ C.stage.c := by
    have h := walkWrites_against_abi C.stage (a := G.xp) (n := 4 * G.nxp)
      (by simp [stage2Regions]) (C.stage.c, stage2CursorExtent)
      (by simp [stage2StagedWrites])
    simpa only [stage2CursorExtent] using h
  -- the body's document window ends inside the document
  have hixExt : f.ix.toNat + f.ext ≤ G.n := by
    have hk1 : C.k + 1 < G.nep := strCount_test G C s hInv f
    have h1 : entryPos G (C.k + 1) < G.n := entryPos_lt G hk1
    have h2 : f.ix.toNat ≤ entryPos G (C.k + 1) := by
      rw [f.hixPos]; exact entryPos_mono G (by omega) hk1
    have h3 : f.ext = entryPos G (C.k + 1) - f.ix.toNat - 1 := f.hext
    omega
  -- the five reads, across the two stores
  have hbaseA : stage2ReadWord (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
        C.stage.c 8 = stage2ReadWord s.mem C.stage.c 8 := by
    rw [hmem8]; unfold stage2ReadWord
    rw [walkReadBytes_two_writes (v := wordBytes 8 (C.k + 2))
      (w := natToBytes (BitVec.ofNat 64 0).toNat 8) (c := C.stage.c) (nt := G.next0)
      (addr := C.stage.c) (n := 8) (Or.inl (by omega)) (Or.inl (by omega))]
  have hxjA : stage2ReadWord (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
        (G.next0 + 12) 8 = stage2ReadWord s.mem (G.next0 + 12) 8 := by
    rw [hmem8]; unfold stage2ReadWord
    rw [walkReadBytes_two_writes (v := wordBytes 8 (C.k + 2))
      (w := natToBytes (BitVec.ofNat 64 0).toNat 8) (c := C.stage.c) (nt := G.next0)
      (addr := G.next0 + 12) (n := 8)
      (Or.inr (by rw [hlen8]; omega)) (Or.inl (by omega))]
  have heA : stage2ReadWord (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
        (C.stage.c + 1112) 8 = stage2ReadWord s.mem (C.stage.c + 1112) 8 := by
    rw [hmem8]; unfold stage2ReadWord
    rw [walkReadBytes_two_writes (v := wordBytes 8 (C.k + 2))
      (w := natToBytes (BitVec.ofNat 64 0).toNat 8) (c := C.stage.c) (nt := G.next0)
      (addr := C.stage.c + 1112) (n := 8)
      (Or.inr (by rw [hlen8]; omega)) (Or.inl (by omega))]
  have hbodyA : readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
        (G.b + f.ix.toNat + 1) (BitVec.ofNat 64 f.ext).toNat =
      readBytes s.mem (G.b + f.ix.toNat + 1) (BitVec.ofNat 64 f.ext).toNat := by
    have hLenN : (BitVec.ofNat 64 f.ext).toNat = f.ext := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have h1 := f.hwin
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    rw [hLenN, hmem8]
    refine walkReadBytes_two_writes (v := wordBytes 8 (C.k + 2))
      (w := natToBytes (BitVec.ofNat 64 0).toNat 8) (c := C.stage.c) (nt := G.next0)
      (addr := G.b + f.ix.toNat + 1) (n := f.ext) ?_ (Or.inl (by omega))
    rcases hdocC with h | h
    · right; rw [hlen8]; omega
    · left; omega
  have hNxpN : (BitVec.ofNat 64 G.nxp).toNat = G.nxp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.nxpLt]
  have hpsA : readLanes32 (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem G.xp
        (BitVec.ofNat 64 G.nxp).toNat =
      readLanes32 s.mem G.xp (BitVec.ofNat 64 G.nxp).toNat := by
    rw [hNxpN, hmem8]
    rw [walkReadLanes32_writeBytes_outside
        (m := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)))
        (start := G.next0 + 20) (v := natToBytes (BitVec.ofNat 64 0).toNat 8)
        (addr := G.xp) (k := G.nxp) (Or.inl (by omega)),
      walkReadLanes32_writeBytes_outside (m := s.mem) (start := C.stage.c + 32)
        (v := wordBytes 8 (C.k + 2)) (addr := G.xp) (k := G.nxp) ?_]
    rcases hxpC with h | h
    · right; rw [hlen8]; omega
    · left; omega
  -- presence is monotone through the two stores
  have hpres : ∀ a n, readBytes s.mem a n ≠ none →
      readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem a n ≠ none := by
    intro a n h
    rw [hmem8]
    have hb : HasBytes s.mem a n := by
      unfold HasBytes
      cases hr : readBytes s.mem a n with
      | none => exact absurd hr h
      | some vs => exact ⟨vs, rfl⟩
    obtain h1 := hasBytes_writeBytes (m := s.mem) hb
      (start := C.stage.c + 32) (bs := wordBytes 8 (C.k + 2))
    obtain ⟨vs2, h2⟩ := hasBytes_writeBytes
      (m := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2))) h1
      (start := G.next0 + 20) (bs := natToBytes (BitVec.ofNat 64 0).toNat 8)
    intro hcon
    rw [h2] at hcon
    exact absurd hcon (by simp)
  have hpre8 : s2StringBodyPre
      [.ptr C.stage.c, .ptr (G.b + f.ix.toNat + 1), .int 64 (BitVec.ofNat 64 f.ext),
       .ptr (G.dst + f.A.toNat), .ptr (G.next0 + 20), .ptr G.xp,
       .ptr (G.next0 + 12), .int 64 (BitVec.ofNat 64 G.nxp)]
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next :=
    s2StringBodyPre_of_reads hbaseA hxjA heA hpsA hbodyA hpres f.hpreS
  -- the callee's answer: `s2StringBody_answers` at the transported precondition,
  -- and the word `s2StringBody_sound`'s post gives
  obtain ⟨r, hcallR⟩ := s2StringBody_answers hpre8
  have hpost8 : s2StringBodyPost
      [.ptr C.stage.c, .ptr (G.b + f.ix.toNat + 1), .int 64 (BitVec.ofNat 64 f.ext),
       .ptr (G.dst + f.A.toNat), .ptr (G.next0 + 20), .ptr G.xp,
       .ptr (G.next0 + 12), .int 64 (BitVec.ofNat 64 G.nxp)]
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next r :=
    s2StringBody_sound hpre8 hcallR
  have hp8 := hpost8
  obtain ⟨m8, form8, slot8, hm8, hret8, hrmem8, hrnext8⟩ := hp8
  have hLenN : (BitVec.ofNat 64 f.ext).toNat = f.ext := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have h1 := f.hwin
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  -- the bundle's own answer names the form the callee takes at the call's memory:
  -- the five words the model reads agree at the two memories
  have hyForm : f.y = BitVec.ofNat 32 form8 :=
    stage2StringBody_head_form (mem := s.mem)
      (mem' := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem)
      (c := C.stage.c) (p := G.b + f.ix.toNat + 1) (dst := G.dst + f.A.toNat)
      (outn := G.next0 + 20) (xp := G.xp) (xj := G.next0 + 12)
      (len := BitVec.ofNat 64 f.ext) (nxp := BitVec.ofNat 64 G.nxp)
      hbaseA hxjA heA hpsA hbodyA f.hpreS f.hy hm8
  have hretRr : r.ret = .int 32 f.y := hret8.trans (by rw [← hyForm])
  have hform0 : form8 ≠ 0 := by
    intro h0
    have hR8' : evalICmp .slt (BitVec.ofNat 32 form8) (BitVec.ofNat 32 1) = 0 := by
      rw [← hyForm]; exact hR8
    rw [h0] at hR8'
    exact absurd hR8' (by decide)
  -- the arm's four write entries, from the callee's model
  obtain ⟨⟨base8, hbase8⟩, ⟨j0_8, hj0_8⟩, ⟨ps8, hps8⟩, ⟨body8, hbody8⟩, ⟨e8, he8⟩,
    hsp8⟩ := s2StringBodyPre_components hpre8
  have hm8' : stage2StringBody (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      C.stage.c (G.b + f.ix.toNat + 1) f.ext (G.dst + f.A.toNat) (G.next0 + 20)
      G.xp (G.next0 + 12) G.nxp = some (m8, form8, slot8) := by
    simpa only [hLenN, hNxpN] using hm8
  have hps8' : readLanes32 (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem G.xp G.nxp
      = some ps8 := by
    simpa only [hNxpN] using hps8
  have hsp8' : BodyPositionsSpaced (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      C.stage.c (G.next0 + 12) G.xp G.nxp (G.b + f.ix.toNat + 1) f.ext := by
    simpa only [hNxpN, hLenN] using hsp8
  have hfr4 : UnchangedOutside (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem r.mem
      [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + f.A.toNat, f.ext),
        (s.next, 8)] := by
    rw [hrmem8]
    exact s2StringBody_frame_of_form (mem := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem)
      (c := C.stage.c) (p := G.b + f.ix.toNat + 1) (len := f.ext)
      (dst := G.dst + f.A.toNat) (outn := G.next0 + 20) (xp := G.xp)
      (xj := G.next0 + 12) (nxp := G.nxp)
      (next := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next)
      hbase8 hj0_8 hps8' hsp8' hm8' hform0
  -- the crossings at that frame
  have hAwin8 : f.A.toNat + f.ext ≤ G.ndst0 + G.n + stage2ArenaReserve := by
    have h1 := hInv8.alen_le
    have h2 := f.hwin
    omega
  obtain ⟨hownedR, hlogR, hevR, hstTyR, hstStR⟩ :=
    s2StringBodyFrame_facts (G := G) (C := strC₈ C f.ix f.ext)
      (s := strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) hInv8
      (p := f.ix.toNat) (A := f.A.toNat) (ext := f.ext) (len := f.ext) (r := r)
      hpost8 hfr4 hAwin8
  -- the run's own silence across the two stores, grown to the call's cursors
  have hfw1 : UnchangedOutside m0
      (writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)))
      (walkWideAt G C (s.next - G.next0)) := by
    refine hInv.frame.write_inside ?_
    intro k hk
    have hk8 : k < 8 := by rw [hlen8] at hk; exact hk
    exact walkWideAt_of_seven
      ⟨(C.stage.c, stage2CursorExtent), by simp [stage2StagedWrites],
        by show C.stage.c ≤ C.stage.c + 32 + k; omega,
        by show C.stage.c + 32 + k < C.stage.c + stage2CursorExtent
           simp only [stage2CursorExtent]; omega⟩
  have hfw2 : UnchangedOutside m0
      (writeBytes (writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)))
        (G.next0 + 20) (natToBytes (BitVec.ofNat 64 0).toNat 8))
      (walkWideAt G C (s.next - G.next0)) := by
    refine hfw1.write_inside ?_
    intro k hk
    have hk8 : k < 8 := by rw [hzero8] at hk; exact hk
    refine walkWideAt_alloca (C := C) (n := s.next - G.next0) ?_ ?_
    · show G.next0 ≤ G.next0 + 20 + k; omega
    · show G.next0 + 20 + k < G.next0 + (s.next - G.next0)
      have hge := hInv.next_ge
      simp only [stage2BootstrapExtent] at hge
      omega
  have hgrowW : UnchangedOutside m0
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      (walkWideAt G (strC₉ C f.ix f.ext) (r.next - G.next0)) := by
    refine UnchangedOutside.of_covered
      (mem := m0) (m := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem)
      (R := walkWideAt G C (s.next - G.next0))
      (R' := walkWideAt G (strC₉ C f.ix f.ext) (r.next - G.next0)) ?_ ?_
    · rw [hmem8]; exact hfw2
    · have hala : C.alen ≤ (strC₉ C f.ix f.ext).alen := by
        show C.alen ≤ C.alen + f.ext; omega
      have hevl : C.evlen ≤ (strC₉ C f.ix f.ext).evlen := le_rfl
      have hstage : (strC₉ C f.ix f.ext).stage = C.stage := rfl
      have hn : s.next - G.next0 ≤ r.next - G.next0 := by
        have hnext : r.next = s.next + 8 := by rw [hrnext8]; rfl
        omega
      exact walkWideAt_grow hala hevl hstage hn
  have hframeR : UnchangedOutside m0 r.mem
      (walkWideAt G (strC₉ C f.ix f.ext) (r.next - G.next0)) := by
    refine hgrowW.trans' ?_
    have hnext8 : G.next0 + stage2BootstrapExtent
        ≤ (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next := hInv8.next_ge
    have hm8c : (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next + 8
        ≤ G.next0 + (r.next - G.next0) := by omega
    exact s2StringBodyFrame_walkWideAt (C := strC₈ C f.ix f.ext)
      (mem := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem)
      (next := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next)
      (m := r.next - G.next0) (r := r) (A := f.A.toNat) (ext := f.ext)
      (len := f.ext) hAle8 le_rfl hnext8 hm8c hfr4
  -- the root slot is outside the crossed footprint, so its presence is the
  -- head's: the frame re-reads it at the callee's memory
  have hrootR : HasBytes r.mem (G.next0 + 8) 4 := by
    obtain ⟨vs, hvs⟩ := hInv8.root_slot
    refine ⟨vs, ?_⟩
    rw [readBytes_frame hfr4 ?_]
    · exact hvs
    · intro i hi q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · intro hcon; omega
      · intro hcon; omega
      · intro hcon
        have hroom := G.arenaRoom
        have hwm : G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ G.next0 :=
          G.watermark (G.dst, G.ndst0 + G.n + stage2ArenaReserve)
            (by simp [stage2Regions])
        omega
      · intro hcon
        have hge := hInv.next_ge
        simp only [stage2BootstrapExtent] at hge
        omega
  obtain ⟨s9, hl9, hs9⟩ :=
    WalkLink.z_arena_reserve_exit (G := G) (C := strC₈ C f.ix f.ext)
      (s := strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) hInv8 rfl
      (p := f.ix.toNat) (off := C.alen) (ext := f.ext) hpend8 (A := f.A)
      hz36 hpos hreadA8 har8 G.dstLt hreadAr8 harr hsub8 hc8 houtn8 hxp8 hxj8 hnxp8
      f.hwin (r := r) hcallR hframeR hownedR hrootR hlogR hevR hstTyR hstStR
  have hs9' : s9 = strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s := hs9
  subst hs9'
  have hl9' : WalkLink (stage2Calls stage2SubCalls) G (strC₈ C f.ix f.ext)
      (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s) (strC₉ C f.ix f.ext)
      (strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := by
    simpa only [strC₉] using hl9
  -- the log's base word at the answer's memory: the head's word carried across
  -- link 8's two stores and the callee's log-silence
  have hzBase8 : readBytes (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).mem
      C.stage.z 8 = readBytes s.mem C.stage.z 8 := by
    simpa using hlogRead 0 (by decide)
  have hlogBaseR : readBytes r.mem C.stage.z 8 = some (wordBytes 8 G.ev) := by
    refine (hlogR 0 8 (by simp only [stage2LogExtent]; omega)).trans ?_
    exact hzBase8.trans hlogBase
  -- the decoded length at the answer's memory, through the private slot's write
  have houtnR : ∃ l, readBytes r.mem (G.next0 + 20) 8 = some (wordBytes 8 l) ∧
      l ≤ f.ext := by
    obtain ⟨l, hr, hle⟩ := s2StringBody_outn_le hm8 hsp8 hform0
    have hsep := s2StringBodyPre_next_outn hpre8
    have hslot := stage2StringBody_slot_le hbase8 hj0_8 hps8' hm8'
    have hread : readBytes
        (writeBytes m8 (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next slot8)
        (G.next0 + 20) 8 = some (wordBytes 8 l) := by
      refine (walkReadBytes_writeBytes_outside (m := m8) (v := slot8)
        (start := (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).next)
        (addr := G.next0 + 20) (n := 8) ?_).trans hr
      rcases hsep with h | h
      · exact Or.inr (by omega)
      · exact Or.inl h
    rw [hrmem8]
    exact ⟨l, hread, by simpa only [hLenN] using hle⟩
  exact ⟨r, _, hseg8.trans (WalkSegment.of_link hl9'), rfl, hretRr, hlogBaseR, houtnR⟩

/-- **Links 1 to 10 compose: `NodeBlock31`'s edge.**  `strPath9`'s endpoint, then
the block's own test — `%call272.i` is the callee's answer and its bit is R8's, so
the edge is `LeafBlock29` and the target is `strS₁₀`. -/
theorem strPath10 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s)
    (hsp0 : C.sp = 0)
    (harr : lookupName (strS₈ G C f.q f.rd f.xv f.A f.Cc f.ix s).env "%arrayidx10.i"
      = some (.ptr (G.b + f.ix.toNat)))
    (hreadAr : readBytes s.mem (C.stage.z + 40) 8 = some (wordBytes 8 G.dst))
    (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0)
    (hlogBase : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)) :
    ∃ (r : CallOutcome) (s' : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s (strC₁₀ C f.ix f.ext) s' 10 ∧
      s' = strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s ∧
      r.ret = .int 32 f.y ∧
      readBytes r.mem C.stage.z 8 = some (wordBytes 8 G.ev) ∧
      (∃ l, readBytes r.mem (G.next0 + 20) 8 = some (wordBytes 8 l) ∧ l ≤ f.ext) := by
  obtain ⟨r, s9, hseg9, hs9, hretR, hlogBaseR, houtnR⟩ :=
    strPath9 G C s hhead hInv f hsp0 harr hreadAr hR8 hlogBase
  subst hs9
  -- ---- link 10: `NodeBlock31`
  have hInv9 : WalkInv G (strC₉ C f.ix f.ext)
      (strS₉ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := hseg9.inv'
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
  exact ⟨r, _, hseg9.trans (WalkSegment.of_link hl10'), rfl, hretR, hlogBaseR, houtnR⟩

/-! ### Links 11 to 15: the residue, and the segment's proof

`strPath10` reaches `LeafBlock29`'s state.  The five links that remain are the
answer's own test, the two arms it selects, the arena merge, the record and the
container's advance.  Four of them already name their targets
(`LeafBlock29_at`, `if_then281_i`, `if_else285_i_at`, `if_end290_i`,
`if_then328_i`); `if.else334_i`'s is `callQuiet`'s existential, which
`WalkLink.if_else334_i_at` exposes by taking the helper's answer as a parameter.

**The residue.**  Everything the five links read is the head bundle's, `WalkInv`'s,
or the previous link's target: `HstringResidue` is empty, and the accepting-arm
selector is the arm's own (`HcontArm.twoEntry`).  The inputs the links used to take
separately are derived here:

* **the answer and its word (R1)** — `strPath10` returns the answer, its call and
  its word: `s2StringBody_answers` at the transported precondition and
  `stage2StringBody_head_form`, which carries the head bundle's form to the call's
  memory.  The body's six memory clauses are not fields either;
* **the decoded length (R2)** — `strPath10` returns `l`, its read at `%outn.i` and
  `l ≤ ext`, from `s2StringBody_outn_le` and `s2StringBody_outn_at_call`;
* **the log's arena-base word (R5)** — `WalkInv.log_dst` at the head's memory, and
  `strPath9` carries it to the answer's, where `z_arena_reserve.exit` reads `%ar`;
* **the log's base word (R3)** — `WalkInv.log_base` at the head's memory, and
  `strPath9` carries it to the answer's, so this section reads it at `r.mem`
  without a premise about the callee;
* **the widths and the cursor's signed bound** — `WalkGeom.dstLt`, `evLt` and
  `ev63` (`stage2Pre`'s clauses), the last through `WalkInv.evlen_le`;
* **the event count** — `WalkInv.events_le_of_tight` at the loop head, where the
  block-keyed allowance is zero, gives `C.events.length ≤ C.k`; the head's guard
  gives `C.k < G.nep`.  `if.then328.i` takes the pair.

Nothing remains in the structure: the two log words are `WalkInv`'s `log_base`
(R3, `%z`'s base word) and `log_dst` (R5, `%ar`'s arena-base word), read at the
head, and outside it only the per-iteration register `%arrayidx10.i` (produced by
`strArr_of_iter`) and the accepting-arm selector R8 (`HcontArm.twoEntry`'s field)
are premises.  `%c.i`, `%z`, `%xp` and `%nxp` are not among them — the static
carrier names all four — so each of the five links reads them through
`WalkInv.regs` at its own state.  The composition is a proof from these; nothing
here is weakened to make one go through.

**The states mirror their links.**  Each `strSₙ` below is written to be the
*state the link concludes*, byte for byte, so the cast `hlₙ' : WalkLink …` is the
link itself and a reader sees which arm a `def` fixes.  The two `if`s — the
answer's own test and the reserve's — stay in the states and in the carries; only
a consumer that needs the *name* rewrites them (`hblock` and the predecessor). -/

/-- **`%arrayidx10.i` at the state link 8 leaves is the header's register, read at
the carried index.**  `while.body.i` binds the name on every pass
(`%arrayidx10.i = %3 + %idxprom.i`), so it is a per-iteration carrier rather than a
static one: its value moves with `C.k` and `walkStaticRegs` can never hold it.  The
clause that carries it is `WalkIter.regarr` — `%7` and `%8` are the header's two
*reads*, and this is the address the header *forms* from them, so the clause
`lookupName env "%arrayidx10.i" = some (.ptr (G.b + entryPos G k))` is produced by
`whileBody_step`'s `getelementptr` over `%3 = G.b` (`WalkPtrs`) and `%7`'s lane
(`WalkIter.reg7`), and preserved by `WalkIter.bind`/`WalkIter.cells_of` exactly as
`%7` is.

This theorem is that clause read at `strS₈`'s environment.  None of the path's
eight links binds `%arrayidx10.i`, so nothing but `stateAt`'s and `bind`'s
pass-through separates the head's cell from the one the call reads, and the
composition reads the head's clause from `WalkInv.iter.regarr`. -/
theorem strArr_of_iter {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {f : HstringFacts G C s} {q : Nat} {rd x : BitVec 32} {A Cc ix : BitVec 64}
    (h : lookupName s.env "%arrayidx10.i" = some (.ptr (G.b + entryPos G C.k))) :
    lookupName (strS₈ G C q rd x A Cc ix s).env "%arrayidx10.i"
      = some (.ptr (G.b + f.ix.toNat)) := by
  rw [f.hixPos]
  simp only [strS₁, strS₂, strS₃, strS₄, strS₅, strS₆, strS₇, strS₈,
    walkIfEnd256OutAt, stateAt, State.bind]
  block_lk

/-- **The two-entry token's path's residue.**  The facts the fifteen links need
beside `WalkInv`'s clauses and the head bundle's fields, at the head state the
bundle is stated at.

**Two fields, and the eleven the structure used to carry are derived.**  Each
derivation names where it happens:

* the callee's answer `r` and its call are `s2StringBody_answers` at the
  transported precondition, inside `strPath9`; its word is
  `stage2StringBody_head_form`'s — on `stage2StringBody_form_congr`, the head
  bundle's `hy` names the form at the head's memory, the congruence carries that
  form to link 8's memory, and the post's own word at the callee's memory is then
  the answer's;
* the decoded length `l` at the write-back's memory and its bound are
  `s2StringBody_outn_le` with `s2StringBody_outn_at_call`, which moves the word
  across the private slot's write at the call's `next`;
* the log's base word at the answer's memory is the head's carried across link 8's
  two stores (`walkReadBytes_two_writes`, `walkReadBytes_log_of_cursorK`) and the
  callee's frame (`s2StringBodyFrame_facts`' log-silence);
* the arena's and the event stream's addresses are `WalkGeom.dstLt`/`evLt`
  (`stage2Pre`'s clauses), the event cursor's signed bound is `WalkGeom.ev63` with
  `WalkInv.evlen_le`, and the event count is
  `WalkInv.events_le_of_tight` at the loop head;
* the accepting-arm selector is `HcontArm.twoEntry`'s, not the residue's: the call
  may refuse, and a refusing answer leaves `NodeBlock31` at `cleanup339.critedge.i`
  rather than reaching the merge.

**The residue is empty.**  Both words are `WalkInv` clauses — `log_dst` at `%z + 40`
and `log_base` at `%z` — read at the **head state's** memory, which is where the
walk layer's clauses live: `%z`'s first eight bytes and its arena-base word lie
inside the walk's write extent, so `WalkInv.frame` — silence *outside* it — says
nothing about them, and `WalkInv.owned` gives the object's presence rather than the
value it holds.  Neither word is written by any block of the walk — `entry`'s
initialisation stores `%ev` at `%z` and `%dst` at `%ar`, and the dispatched blocks
write `%z + 8`, the `memset` at `%z + 24` and `%z + 48` only — so each step's own
write list preserves the pair.  `stringPath_seg` reads them off the head invariant
and `strPath9` carries each across link 8's two stores to the call's memory, which
is all the five links read.  The structure stays as the arm's field so a future
memory fact has a named home; it carries nothing today. -/
structure HstringResidue {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HstringFacts G C s) : Prop

/-- **The residue at every head state**, as the premise a producer supplies: one
bank of facts per head state, read at the bundle's own state. -/
abbrev WalkStringResidue {m0 : Mem} (G : WalkGeom m0) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (f : HstringFacts G C s) → HstringResidue G C s f

/-- The literal arm's `%or.i`: the position's successor with the high bit set. -/
def strOr (x7 : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (x7 + BitVec.ofNat 32 1).toNat ||| BitVec.ofNat 64 9223372036854775808

/-- **The state `LeafBlock29` reaches**: the answer's own test on `1`. -/
def strS₁₁ (y : BitVec 32) (t : State) : State :=
  { (t.bind "%SwitchLeaf30" (.int 1 (evalICmp .eq y (BitVec.ofNat 32 1)))) with
    pc := (if evalICmp .eq y (BitVec.ofNat 32 1) = 1 then "if.then281.i"
      else "if.else285.i"),
    pre := some t.pc }

/-- **The state `if.then281.i` reaches**: the literal's `add`, `zext` and `or`. -/
def strS₁₂t (x7 : BitVec 32) (t : State) : State :=
  { stateAt (cells [
      ("%or.i", .int 64 (strOr x7)),
      ("%conv284.i", .int 64 (BitVec.ofNat 64 (x7 + BitVec.ofNat 32 1).toNat)),
      ("%add283.i", .int 32 (x7 + BitVec.ofNat 32 1))] t.env) t with
    pc := "if.end290.i", pre := some t.pc }

/-- **The state `if.end290.i` reaches**, the reserve's own test keeping the
edge — so this is the block's target and the arm is the test's. -/
def strS₁₃ (e₁ e₂ nl nc : BitVec 64) (t : State) : State :=
  { stateAt (("%cmp.not.i85", .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 13) nc)) ::
      ("%add.i84", .int 64 (nl + BitVec.ofNat 64 13)) ::
      ("%z.val33", .int 64 nc) :: ("%z.val", .int 64 nl) ::
      ("%.sink", .int 64 e₂) :: ("%conv286.i.sink.in", .int 64 e₁) :: t.env) t with
    pc := (if evalICmp .ugt (nl + BitVec.ofNat 64 13) nc = 1 then "if.end.i86"
      else "if.then328.i"),
    pre := some t.pc }

/-- **The state `if.then328.i` reaches**: the record appended at the event
cursor. -/
def strS₁₄ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sinkIn span : BitVec 64)
    (t : State) : State :=
  walkIfThen328OutAt G C t sinkIn (0 : BitVec 1) span

/-- **The state `if.else334.i` reaches**: the container's advance, at the
merge. -/
def strS₁₅ (r : CallOutcome) (t : State) : State :=
  { stateAt t.env { t with mem := r.mem, next := r.next } with
    pc := "cleanup478.i", pre := some t.pc }

/-- The merge's first `phi` off `if.then281.i`. -/
theorem strMergePhiThen₁ :
    phiIncoming "if.then281.i"
      [("if.then281.i", (Operand.reg "%sub260.i")),
       ("if.else285.i", (Operand.reg "%32"))] = some (.reg "%sub260.i") := by
  decide

/-- The merge's first `phi` off `if.else285.i`. -/
theorem strMergePhiElse₁ :
    phiIncoming "if.else285.i"
      [("if.then281.i", (Operand.reg "%sub260.i")),
       ("if.else285.i", (Operand.reg "%32"))] = some (.reg "%32") := by
  decide

/-- The merge's second `phi` off `if.then281.i`. -/
theorem strMergePhiThen₂ :
    phiIncoming "if.then281.i"
      [("if.then281.i", (Operand.reg "%or.i")),
       ("if.else285.i", (Operand.reg "%z.val36"))] = some (.reg "%or.i") := by
  decide

/-- The merge's second `phi` off `if.else285.i`. -/
theorem strMergePhiElse₂ :
    phiIncoming "if.else285.i"
      [("if.then281.i", (Operand.reg "%or.i")),
       ("if.else285.i", (Operand.reg "%z.val36"))] = some (.reg "%z.val36") := by
  decide

/-- **The two-entry token's path to the merge.**  The fifteen links composed: the
segment's endpoint is the merge's state at the callee's answer and the write-back's
length, and its two register cells are the merge's own.

**The parameters.**  `R` is `HstringResidue`, which carries nothing: the two words
the path reads are `WalkInv`'s `log_dst` and `log_base` at the head state, and
`stringPath_seg` reads them off `hInv`.  The residue stays in the signature because
it is the arm's field.  `hR8` is the arm's selector, carried here rather than by the
residue because the callee may refuse and a refusal leaves `NodeBlock31` at
`cleanup339.critedge.i`.  The head facts it does not restate are the bundle's:
`f.hcount` gives the continuing test (`strCount_test`), `f.hwin` the window's room,
and the parameter `hsp0` the depth that makes `if.else334.i`'s precondition an
`Or.inl`.
Nothing is quantified over states the run does not reach: the endpoint is the state
the last link leaves.

**The two arms.**  `LeafBlock29`'s edge is the answer's own test on `1`; both arms
are taken, one link each, and they converge on `if.end290.i` with the same carry.
The literal arm's cells are the position's successor with the high bit, and the
write-back arm's are the decoded length; the merge's two `phi`s select them by the
predecessor, which is why the arm has to be a case rather than a value. -/
theorem stringPath_seg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s) (f : HstringFacts G C s)
    (hsp0 : C.sp = 0)
    (R : HstringResidue G C s f)
    (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0) :
    ∃ (Cd : WalkCarry G) (sd : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 15 ∧
      Cd.block = "cleanup478.i" ∧ Cd.k = C.k ∧
      sd.pre = some "if.else334.i" ∧ WalkInv G Cd sd ∧
      lookupName sd.env "%inc208.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 2))) ∧
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
  obtain ⟨r, s10, hseg10, hs10, hretR, hlogBaseR, ⟨l, hreadOutn, hlext⟩⟩ :=
    strPath10 G C s hhead hInv f hsp0 (strArr_of_iter (f := f) hInv.iter.regarr)
      hInv.log_dst hR8 hInv.log_base
  subst hs10
  -- the event cursor's signed bound: the staging's clause, through `evlen_le`
  have hev63 : C.evlen < 2 ^ 63 := by
    have h1 := hInv.evlen_le
    have h2 := G.ev63
    omega
  have hInv10 : WalkInv G (strC₁₀ C f.ix f.ext)
      (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := hseg10.inv'
  have hev64 : C.evlen < 2 ^ 64 := by
    have h1 := hInv.evlen_le
    have h2 := G.evRoom
    have h3 := G.evcapLt
    simp only [stage2RecordBytes] at h1 h2
    omega
  have hk1 : C.k + 1 < G.nep := strCount_test G C s hInv f
  -- the head is outside the append stretch, so `events_le`'s allowance is zero here: the
  -- trace's count is the entries consumed, and the head's entry is still to come
  have hblockEmit : walkEmitC C.block = 0 := by
    rw [hhead]
    exact walkEmitC_of_not_contains (by decide)
  have htight : C.events.length ≤ C.k := WalkInv.events_le_of_tight hInv hblockEmit
  have hkltC : C.k < G.nep := by omega
  obtain ⟨-, hclear13⟩ :=
    walkEventReserve_clear (G := G) (C := C) (s := s) hInv hblockEmit (by omega)
  have hcapLt : G.evcap < 2 ^ 64 := G.evcapLt
  -- the reserve's thirteen-byte test is clear at the carried cursor
  have hres13 : evalICmp .ugt ((BitVec.ofNat 64 C.evlen) + BitVec.ofNat 64 13)
      (BitVec.ofNat 64 G.evcap) = 0 := by
    rw [← BitVec.ofNat_add]
    exact walkEvalICmp_ugt_ofNat_zero (a := C.evlen + 13) (b := G.evcap)
      (by omega) G.evcapLt (by omega)
  have hnotres : ¬ ((0 : BitVec 1) = 1) := by decide
  -- ---- link 11: `LeafBlock29`'s own test
  have hcall272 : evalOperand (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)
      (.reg "%call272.i") = some (.int 32 f.y) := by
    simp [strS₁₀, State.bind, strS₉, walkZArenaReserveExitOutAt, strS₈, stateAt,
      evalOperand, lookupName, hretR]
  obtain ⟨s11, hl11, hs11⟩ :=
    WalkLink.LeafBlock29_at (calls := stage2Calls stage2SubCalls) (G := G)
      (C := strC₁₀ C f.ix f.ext)
      (s := strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) hInv10 rfl
      (x1 := f.y) hcall272
  by_cases hy1 : evalICmp .eq f.y (BitVec.ofNat 32 1) = 1
  · -- ===== the literal arm: `if.then281.i` =====
    have hs11' : s11 = strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := hs11
    subst hs11'
    have hl11' : WalkLink (stage2Calls stage2SubCalls) G (strC₁₀ C f.ix f.ext)
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)
        (strC₁₁ C f.ix f.ext f.y)
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) := hl11
    have hInv11 : WalkInv G (strC₁₁ C f.ix f.ext f.y)
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) :=
      hl11'.inv'
    -- `%7`, the literal's operand
    have h7 : lookupName
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)).env "%7"
        = some (.int 32 (BitVec.ofNat 32 (entryPos G C.k))) := by
      simpa [strS₁₁, State.bind, strS₁₀, strS₉, walkZArenaReserveExitOutAt, strS₈,
        walkIfEnd256OutAt, strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, strSetK₅,
        stateAt, cells, lookupName] using f.h7
    obtain ⟨s12, hl12, hs12⟩ :=
      WalkLink.if_then281_i (G := G) (C := strC₁₁ C f.ix f.ext f.y)
        (s := strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
        hInv11
        (by show (if evalICmp .eq f.y (BitVec.ofNat 32 1) = 1 then "if.then281.i" else "if.else285.i") = "if.then281.i"; rw [if_pos hy1])
        (x7 := BitVec.ofNat 32 (entryPos G C.k)) h7
    have hs12' : s12 = strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) := hs12
    subst hs12'
    have hl12' : WalkLink (stage2Calls stage2SubCalls) G (strC₁₁ C f.ix f.ext f.y)
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
        (strC₁₂ C f.ix f.ext f.y)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))) := hl12
    have hInv12 : WalkInv G (strC₁₂ C f.ix f.ext f.y)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))) :=
      hl12'.inv'
    -- the two `phi`s' operands
    have hpre12 : (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))).pre
        = some "if.then281.i" := by
      show some (if evalICmp .eq f.y (BitVec.ofNat 32 1) = 1 then "if.then281.i" else "if.else285.i") = some "if.then281.i"
      rw [if_pos hy1]
    have hsub12 : evalOperand (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))
        (.reg "%sub260.i") = some (.int 64 (BitVec.ofNat 64 f.ext)) := by
      have hval : (BitVec.ofNat 64 f.q)
          + (f.ix ^^^ BitVec.ofNat 64 18446744073709551615) = BitVec.ofNat 64 f.ext :=
        walkSub260_eq (strAdvance G C s hInv f)
      simp [strS₁₂t, strS₁₁, State.bind, strS₁₀, strS₉, walkZArenaReserveExitOutAt,
        strS₈, walkIfEnd256OutAt, strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁,
        strSetK₅, stateAt, cells, lookupName, evalOperand, hval]
    have hor12 : evalOperand (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))
        (.reg "%or.i") = some (.int 64 (strOr (BitVec.ofNat 32 (entryPos G C.k)))) := by
      simp [strS₁₂t, stateAt, cells, lookupName, evalOperand]
    -- ---- link 13: `if.end290.i`
    have hlen12 : lookupName (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))).env "%len"
        = some (.ptr (C.stage.z + 8)) :=
      hInv12.regs ⟨"%len", .ptr (C.stage.z + 8)⟩ (by simp [walkStaticRegs])
    have hreadL12 : readBytes (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))).mem
        (C.stage.z + 8) 8 = some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hev64]
      exact hInv12.log_len
    have hreadC12 : readBytes (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))).mem
        (C.stage.z + 16) 8 = some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.evcapLt]
      exact hInv12.log_cap
    obtain ⟨s13, hl13, hs13⟩ :=
      WalkLink.if_end290_i (G := G) (C := strC₁₂ C f.ix f.ext f.y)
        (s := strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))
        hInv12 rfl (p := "if.then281.i") (op₁ := .reg "%sub260.i")
        (op₂ := .reg "%or.i") (e1 := BitVec.ofNat 64 f.ext)
        (e2 := strOr (BitVec.ofNat 32 (entryPos G C.k)))
        (nl := BitVec.ofNat 64 C.evlen) (nc := BitVec.ofNat 64 G.evcap)
        hpre12 strMergePhiThen₁ hsub12 strMergePhiThen₂ hor12 hlen12
        (hInv12.regs ⟨"%cap", .ptr (C.stage.z + 16)⟩ (by simp [walkStaticRegs]))
        hreadL12 hreadC12
    have hs13' : s13 = strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))) := hs13
    subst hs13'
    have hl13' : WalkLink (stage2Calls stage2SubCalls) G (strC₁₂ C f.ix f.ext f.y)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))
        (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))) := hl13
    have hInv13 : WalkInv G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap))
        (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))) :=
      hl13'.inv'
    -- ---- link 14: `if.then328.i`
    have hsink13 : lookupName (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).env
        "%conv286.i.sink.in" = some (.int 64 (BitVec.ofNat 64 f.ext)) := by
      simp [strS₁₃, stateAt, cells, lookupName]
    have hspan13 : lookupName (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).env
        "%.sink" = some (.int 64 (strOr (BitVec.ofNat 32 (entryPos G C.k)))) := by
      simp [strS₁₃, stateAt, cells, lookupName]
    have hzv13 : lookupName (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).env
        "%z.val" = some (.int 64 (BitVec.ofNat 64 C.evlen)) := by
      simp [strS₁₃, stateAt, cells, lookupName]
    have hadd13 : lookupName (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).env
        "%add.i84" = some (.int 64 (BitVec.ofNat 64 (C.evlen + 13))) := by
      simp [strS₁₃, stateAt, cells, lookupName, BitVec.ofNat_add]
    have hkey13 : lookupName (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).env
        "%key.1.i" = some (.int 1 0) := by
      simp [strS₁₃, strS₁₂t, strS₁₁, State.bind, strS₁₀, strS₉,
        walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt, strS₇, strS₆, strS₅,
        strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells, lookupName]
    have hz13 : lookupName (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).env
        "%z" = some (.ptr C.stage.z) := by
      simpa [strS₁₃, strS₁₂t, strS₁₁, State.bind, strS₁₀, strS₉,
        walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt, strS₇, strS₆, strS₅,
        strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells, lookupName] using hInv.regs ⟨"%z", .ptr C.stage.z⟩ (by simp [walkStaticRegs])
    have hzread13 : readBytes (strS₁₃ (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)
        (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
          (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))).mem
        C.stage.z 8 = some (wordBytes 8 G.ev) := hlogBaseR
    obtain ⟨s14, hl14, hs14⟩ :=
      WalkLink.if_then328_i (G := G) (C := strC₁₃ C f.ix f.ext f.y
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (s := strS₁₃ (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k))) (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))
        hInv13
        (by show (if evalICmp .ugt ((BitVec.ofNat 64 C.evlen) + BitVec.ofNat 64 13) (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i86" else "if.then328.i") = "if.then328.i"; rw [hres13, if_neg hnotres])
        (sinkIn := BitVec.ofNat 64 f.ext) (keyBit := 0)
        (span := strOr (BitVec.ofNat 32 (entryPos G C.k))) hsink13 hz13 hzread13
        hzv13 hev63 hkey13 hspan13 hadd13
        (by show C.evlen + 13 < 2 ^ 64; omega) hlen12
        (hInv13.regs ⟨"%outn.i", .ptr (G.next0 + 20)⟩ (by simp [walkStaticRegs]))
        G.evLt htight hkltC
    have hs14' : s14 = strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k)))
        (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))) := hs14
    subst hs14'
    have hl14' : WalkLink (stage2Calls stage2SubCalls) G
        (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))
        (strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) 0
          (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k))))
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))) := hl14
    have hInv14 : WalkInv G (strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) 0 (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))))
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))) :=
      hl14'.inv'
    -- ---- link 15: `if.else334.i`
    have hspv0 : (BitVec.ofNat 32 C.sp).toNat = 0 := by rw [hsp0]; decide
    have hpreAV : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst]
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))).mem
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))).next :=
      ⟨BitVec.ofNat 32 C.sp, G.next0 + 8, C.stage.ctype, C.stage.cst, rfl, Or.inl hspv0⟩
    obtain ⟨r₂, hcall₂, -, -⟩ :=
      s2AfterValueContract.resolves (next := (strS₁₄ G (strC₁₃ C f.ix f.ext f.y
        (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k)))
        (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))).next)
        hpreAV
    obtain ⟨s15, hl15, hs15⟩ :=
      WalkLink.if_else334_i_at (G := G)
        (C := strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap) 0 (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k))))
        (s := strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))))
        hInv14
        (by show (if (0 : BitVec 1) = 1 then "if.then330.i" else "if.else334.i") = "if.else334.i"; rw [if_neg hnotres])
        (hInv14.regs ⟨"%root_done.i", .ptr (G.next0 + 8)⟩ (by simp [walkStaticRegs]))
        hpreAV r₂ hcall₂
    have hs15' : s15 = strS₁₅ r₂
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))) := hs15
    subst hs15'
    have hl15' : WalkLink (stage2Calls stage2SubCalls) G
        (strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) 0
          (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k))))
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))))
        (strC₁₅ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) 0
          (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k))))
        (strS₁₅ r₂ (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
          (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
              (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)))))) := hl15
    refine ⟨strC₁₅ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
      0 (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k))),
      strS₁₅ r₂ (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 f.ext)
        (strOr (BitVec.ofNat 32 (entryPos G C.k)))
        (strS₁₃ (BitVec.ofNat 64 f.ext) (strOr (BitVec.ofNat 32 (entryPos G C.k)))
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (strS₁₂t (BitVec.ofNat 32 (entryPos G C.k))
            (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))))),
      ((((hseg10.trans (WalkSegment.of_link hl11')).trans
        (WalkSegment.of_link hl12')).trans (WalkSegment.of_link hl13')).trans
        (WalkSegment.of_link hl14')).trans (WalkSegment.of_link hl15'),
      rfl, rfl, ?_, hl15'.inv', ?_, ?_⟩
    · simp [strS₁₅, strS₁₄, walkIfThen328OutAt, hnotres]
    · simp [strS₁₅, strS₁₄, walkIfThen328OutAt, strS₁₃, strS₁₂t, strS₁₁, State.bind,
        strS₁₀, strS₉, walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt, strS₇,
        strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells, lookupName]
    · simpa [strS₁₅, strS₁₄, walkIfThen328OutAt, strS₁₃, strS₁₂t, strS₁₁, State.bind,
        strS₁₀, strS₉, walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt, strS₇,
        strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells, lookupName]
        using f.hnep
  · -- ===== the write-back arm: `if.else285.i` =====
    have hs11' : s11 = strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s) := hs11
    subst hs11'
    have hl11' : WalkLink (stage2Calls stage2SubCalls) G (strC₁₀ C f.ix f.ext)
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)
        (strC₁₁ C f.ix f.ext f.y)
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) := hl11
    have hInv11 : WalkInv G (strC₁₁ C f.ix f.ext f.y)
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) :=
      hl11'.inv'
    -- the write-back's inputs: `%outn.i`'s word at the callee's memory, the arena
    -- word and the cursor
    have houtn11 : lookupName
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)).env "%outn.i"
        = some (.ptr (G.next0 + 20)) :=
      hInv11.regs ⟨"%outn.i", .ptr (G.next0 + 20)⟩ (by simp [walkStaticRegs])
    have hread11 : readBytes
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)).mem
        (G.next0 + 20) 8 = some (wordBytes 8 l) := hreadOutn
    have hz3611 : lookupName
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)).env "%z.val36"
        = some (.int 64 (BitVec.ofNat 64 f.A.toNat)) := by
      rw [walkOfNat_toNat]
      simp [strS₁₁, State.bind, strS₁₀, strS₉, walkZArenaReserveExitOutAt, strS₈,
        walkIfEnd256OutAt, strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, strSetK₅,
        stateAt, cells, lookupName]
    have hge11 : G.ndst0 ≤ f.A.toNat := by
      obtain ⟨a₀, hge₀, hle₀, hr₀⟩ := hInv.log_alen
      have h1 : natToBytes f.A.toNat 8 = natToBytes a₀ 8 := by
        rw [wordBytes] at hr₀
        exact Option.some.inj (f.hreadA.symm.trans hr₀)
      have h2 := congrArg bytesToNat h1
      rw [natToBytes_toNat, natToBytes_toNat] at h2
      have h3 : f.A.toNat % 256 ^ 8 = f.A.toNat := by
        rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt f.A.isLt]
      have h5 := hInv.alen_le
      have hroom := G.arenaRoom
      have hcap := G.dstcapLt
      simp only [stage2ArenaReserve] at hroom
      have h4 : a₀ % 256 ^ 8 = a₀ := by
        rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt (by omega)]
      omega
    have hal6411 : f.A.toNat + l < 2 ^ 64 := by
      have h1 := hInv.alen_le
      have h2 := f.hwin
      have h3 := G.maxDoc
      have h4 := hInv.logArena_le (A := f.A) f.hreadA
      have h5 := hlext
      simp only [stage2MaxDocument] at h3
      omega
    have hale11 : f.A.toNat + l ≤ (strC₁₁ C f.ix f.ext f.y).alen := by
      have h4 := hInv.logArena_le (A := f.A) f.hreadA
      have h5 := hlext
      show f.A.toNat + l ≤ C.alen + f.ext
      omega
    obtain ⟨s12, hl12, hs12⟩ :=
      WalkLink.if_else285_i_at (G := G) (C := strC₁₁ C f.ix f.ext f.y)
        (s := strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) hInv11
        (by show (if evalICmp .eq f.y (BitVec.ofNat 32 1) = 1 then "if.then281.i" else "if.else285.i") = "if.else285.i"; rw [if_neg hy1])
        (l := l) (a := f.A.toNat) (ao := G.next0 + 20) houtn11 hread11
        (by omega) hz3611
        (hInv11.regs ⟨"%alen", .ptr (C.stage.z + 48)⟩ (by simp [walkStaticRegs]))
        hal6411 hge11 hale11
    have hs12' : s12 = ifElse285OutAt
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
        C.stage.z f.A.toNat l := hs12
    subst hs12'
    have hl12' : WalkLink (stage2Calls stage2SubCalls) G (strC₁₁ C f.ix f.ext f.y)
        (strS₁₁ f.y (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
        (strC₁₂ C f.ix f.ext f.y)
        (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l) := hl12
    have hInv12 : WalkInv G (strC₁₂ C f.ix f.ext f.y)
        (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l) :=
      hl12'.inv'
    -- the two `phi`s' operands: the decoded length and the arena word
    have hpre12 : (ifElse285OutAt (strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l).pre
        = some "if.else285.i" := by
      show some (if evalICmp .eq f.y (BitVec.ofNat 32 1) = 1 then "if.then281.i" else "if.else285.i") = some "if.else285.i"
      rw [if_neg hy1]
    have hsub12 : evalOperand (ifElse285OutAt (strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l)
        (.reg "%32") = some (.int 64 (BitVec.ofNat 64 l)) := by
      simp [ifElse285OutAt, stateAt, cells, lookupName, evalOperand]
    have hor12 : evalOperand (ifElse285OutAt (strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l)
        (.reg "%z.val36") = some (.int 64 (BitVec.ofNat 64 f.A.toNat)) := by
      rw [walkOfNat_toNat]
      simp [ifElse285OutAt, strS₁₁, State.bind, strS₁₀, strS₉, walkZArenaReserveExitOutAt,
        strS₈, walkIfEnd256OutAt, strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁,
        strSetK₅, stateAt, cells, lookupName, evalOperand]
    have hreadL12 : readBytes (ifElse285OutAt (strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l).mem
        (C.stage.z + 8) 8 = some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hev64]
      exact hInv12.log_len
    have hreadC12 : readBytes (ifElse285OutAt (strS₁₁ f.y
        (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l).mem
        (C.stage.z + 16) 8 = some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.evcapLt]
      exact hInv12.log_cap
    obtain ⟨s13, hl13, hs13⟩ :=
      WalkLink.if_end290_i (G := G) (C := strC₁₂ C f.ix f.ext f.y)
        (s := ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l)
        hInv12 rfl (p := "if.else285.i") (op₁ := .reg "%32")
        (op₂ := .reg "%z.val36") (e1 := BitVec.ofNat 64 l)
        (e2 := BitVec.ofNat 64 f.A.toNat) (nl := BitVec.ofNat 64 C.evlen)
        (nc := BitVec.ofNat 64 G.evcap)
        hpre12 strMergePhiElse₁ hsub12 strMergePhiElse₂ hor12
        (hInv12.regs ⟨"%len", .ptr (C.stage.z + 8)⟩ (by simp [walkStaticRegs]))
        (hInv12.regs ⟨"%cap", .ptr (C.stage.z + 16)⟩ (by simp [walkStaticRegs]))
        hreadL12 hreadC12
    have hs13' : s13 = strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
        (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
        (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l) := hs13
    subst hs13'
    have hl13' : WalkLink (stage2Calls stage2SubCalls) G (strC₁₂ C f.ix f.ext f.y)
        (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s)) C.stage.z f.A.toNat l)
        (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l)) := hl13
    have hInv13 : WalkInv G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap))
        (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l)) :=
      hl13'.inv'
    -- ---- link 14: `if.then328.i`
    have hsink13 : lookupName (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).env "%conv286.i.sink.in"
        = some (.int 64 (BitVec.ofNat 64 l)) := by
      simp [strS₁₃, stateAt, cells, lookupName]
    have hspan13 : lookupName (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).env "%.sink"
        = some (.int 64 (BitVec.ofNat 64 f.A.toNat)) := by
      simp [strS₁₃, stateAt, cells, lookupName]
    have hzv13 : lookupName (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).env "%z.val"
        = some (.int 64 (BitVec.ofNat 64 C.evlen)) := by
      simp [strS₁₃, stateAt, cells, lookupName]
    have hadd13 : lookupName (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).env "%add.i84"
        = some (.int 64 (BitVec.ofNat 64 (C.evlen + 13))) := by
      simp [strS₁₃, stateAt, cells, lookupName, BitVec.ofNat_add]
    have hkey13 : lookupName (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).env "%key.1.i" = some (.int 1 0) := by
      simp [strS₁₃, ifElse285OutAt, strS₁₁, State.bind, strS₁₀, strS₉,
        walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt, strS₇, strS₆, strS₅,
        strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells, lookupName]
    have hz13 : lookupName (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).env "%z" = some (.ptr C.stage.z) := by
      simpa [strS₁₃, ifElse285OutAt, strS₁₁, State.bind, strS₁₀, strS₉,
        walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt, strS₇, strS₆, strS₅,
        strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells, lookupName] using hInv.regs ⟨"%z", .ptr C.stage.z⟩ (by simp [walkStaticRegs])
    have hzread13 : readBytes (strS₁₃ (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) (ifElse285OutAt (strS₁₁ f.y
          (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
          C.stage.z f.A.toNat l)).mem C.stage.z 8 = some (wordBytes 8 G.ev) := by
      have hmem : (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l)).mem
          = writeBytes r.mem (C.stage.z + 48) (wordBytes 8 (f.A.toNat + l)) := rfl
      rw [hmem, walkReadBytes_writeBytes_outside (start := C.stage.z + 48)
        (addr := C.stage.z) (n := 8) (v := wordBytes 8 (f.A.toNat + l)) ?_]
      · exact hlogBaseR
      · left
        omega
    obtain ⟨s14, hl14, hs14⟩ :=
      WalkLink.if_then328_i (G := G) (C := strC₁₃ C f.ix f.ext f.y
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (s := strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l))
        hInv13
        (by show (if evalICmp .ugt ((BitVec.ofNat 64 C.evlen) + BitVec.ofNat 64 13) (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i86" else "if.then328.i") = "if.then328.i"; rw [hres13, if_neg hnotres])
        (sinkIn := BitVec.ofNat 64 l) (keyBit := 0)
        (span := BitVec.ofNat 64 f.A.toNat) hsink13 hz13 hzread13 hzv13 hev63 hkey13
        hspan13 hadd13 (by show C.evlen + 13 < 2 ^ 64; omega)
        (hInv13.regs ⟨"%len", .ptr (C.stage.z + 8)⟩ (by simp [walkStaticRegs]))
        (hInv13.regs ⟨"%outn.i", .ptr (G.next0 + 20)⟩ (by simp [walkStaticRegs]))
        G.evLt htight hkltC
    have hs14' : s14 = strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat)
        (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l)) := hs14
    subst hs14'
    have hl14' : WalkLink (stage2Calls stage2SubCalls) G
        (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l))
        (strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) 0
          (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat))
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l))) := hl14
    have hInv14 : WalkInv G (strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap) 0 (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat))
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l))) :=
      hl14'.inv'
    -- ---- link 15: `if.else334.i`
    have hspv0 : (BitVec.ofNat 32 C.sp).toNat = 0 := by rw [hsp0]; decide
    have hpreAV : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst]
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l))).mem
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l))).next :=
      ⟨BitVec.ofNat 32 C.sp, G.next0 + 8, C.stage.ctype, C.stage.cst, rfl, Or.inl hspv0⟩
    obtain ⟨r₂, hcall₂, -, -⟩ :=
      s2AfterValueContract.resolves (next := (strS₁₄ G (strC₁₃ C f.ix f.ext f.y
        (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat)
        (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l))).next) hpreAV
    obtain ⟨s15, hl15, hs15⟩ :=
      WalkLink.if_else334_i_at (G := G)
        (C := strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap) 0 (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat))
        (s := strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l)))
        hInv14
        (by show (if (0 : BitVec 1) = 1 then "if.then330.i" else "if.else334.i") = "if.else334.i"; rw [if_neg hnotres])
        (hInv14.regs ⟨"%root_done.i", .ptr (G.next0 + 8)⟩ (by simp [walkStaticRegs]))
        hpreAV r₂ hcall₂
    have hs15' : s15 = strS₁₅ r₂
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l))) := hs15
    subst hs15'
    have hl15' : WalkLink (stage2Calls stage2SubCalls) G
        (strC₁₄ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) 0
          (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat))
        (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l)))
        (strC₁₅ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) 0
          (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat))
        (strS₁₅ r₂ (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
          (BitVec.ofNat 64 f.A.toNat)
          (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
            (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
            (ifElse285OutAt (strS₁₁ f.y
              (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
              C.stage.z f.A.toNat l)))) := hl15
    refine ⟨strC₁₅ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
      0 (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat),
      strS₁₅ r₂ (strS₁₄ G (strC₁₃ C f.ix f.ext f.y (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 64 l)
        (BitVec.ofNat 64 f.A.toNat)
        (strS₁₃ (BitVec.ofNat 64 l) (BitVec.ofNat 64 f.A.toNat)
          (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)
          (ifElse285OutAt (strS₁₁ f.y
            (strS₁₀ G C f.q f.rd f.xv f.A f.Cc f.ix f.ext r s))
            C.stage.z f.A.toNat l))),
      ((((hseg10.trans (WalkSegment.of_link hl11')).trans
        (WalkSegment.of_link hl12')).trans (WalkSegment.of_link hl13')).trans
        (WalkSegment.of_link hl14')).trans (WalkSegment.of_link hl15'),
      rfl, rfl, ?_, hl15'.inv', ?_, ?_⟩
    · simp [strS₁₅, strS₁₄, walkIfThen328OutAt, hnotres]
    · simp [strS₁₅, strS₁₄, walkIfThen328OutAt, strS₁₃, ifElse285OutAt, strS₁₁,
        State.bind, strS₁₀, strS₉, walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt,
        strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells,
        lookupName]
    · simpa [strS₁₅, strS₁₄, walkIfThen328OutAt, strS₁₃, ifElse285OutAt, strS₁₁,
        State.bind, strS₁₀, strS₉, walkZArenaReserveExitOutAt, strS₈, walkIfEnd256OutAt,
        strS₇, strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, strSetK₅, stateAt, cells,
        lookupName] using f.hnep

/-! ### The merge arm

The arm `standaloneString_finish` states as an outcome, as a
`WalkDispatchResult`: the merge at `k2 = C.k + 2` and `%nep = G.nep`, the depth
the invariant carries, and the price `15 + 2 ≤ 32·2 + 8·(entryPos G (C.k+2) −
entryPos G C.k)`, which the two-entry advance alone pays.  Everything it reads is
`stringPath_seg`'s conclusion: the segment, its endpoint, the endpoint's two
cells and the invariant at it. -/

/-- **The `merge` arm from the two-entry bundle.**  The dispatch reaches
`cleanup478.i` at `%k.2.i = %inc208.i = %k.0.i249 + 2`, so the index advanced by
two and the entry count is `G.nep`; the classification is the merge's own test
on that index (`WalkDispatchResult.toOutcome`), which at `C.k = 0`,
`G.nep = 2` reads `2 < 2` — false — and gives the `finish` the standalone string
is.  No premise tests `C.k + 1 < G.nep` here: that test is the head's, and it is
what selects *which bundle* describes the state, not what the dispatch does.

The residue is a parameter rather than a field of the bundle: what the fifteen
links need beside the invariant and the bundle's own facts is `HstringResidue`,
which is empty — both words are the invariant's (`log_dst`, `log_base`) — and the
bundle states the token's facts, not the path's witnesses.  `hR8` is the arm's own
selector, beside the residue: the same call can refuse, and a refusing answer
leaves `NodeBlock31` at `cleanup339.critedge.i` instead of reaching this
merge.

**Why this arm builds `merge` and not `mergeLast`.**  Its index is `C.k + 2`, so the
byte span it crossed is the two entries' and the price states it; only at a two-entry
stream (`C.k = 0`, `G.nep = 2`) does that index reach the stream's end, and the arm does
not know which of those documents it is at.  `mergeLast` would therefore be unusable
here, and the full price is the one the two-entry advance pays. -/
theorem WalkDispatchResult.ofStringMerge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hhead : C.block = "NodeBlock21") (hInv : WalkInv G C s)
    (f : HstringFacts G C s) (hsp0 : C.sp = 0) (R : HstringResidue G C s f)
    (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨Cd, sd, hseg, hsegBlock, hsegK, hsegPre, hInvD, hinc208, hnepM⟩ :=
    stringPath_seg G C s hhead hInv f hsp0 R hR8
  have hk2cap : C.k + 2 ≤ G.nep := by
    have := strCount_test G C s hInv f
    omega
  have hnep64 : G.nep < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
  refine WalkDispatchResult.merge Cd sd 15 Cd.sp (C.k + 2) "if.else334.i"
    (Operand.reg "%sp.i.0248") (Operand.reg "%inc208.i") (BitVec.ofNat 64 G.nep)
    hseg hsegBlock hsegK hsegPre ?_ ?_ ?_ ?_ hnepM ?_ ?_ ?_ ?_ ?_
  · -- the merge's depth `phi` takes `%sp.i.0248` on the `if.else334.i` edge
    exact stringCleanupSpIncoming_at
  · -- and that register is the depth the endpoint's invariant carries
    exact LeanLLVM.evalOperand_reg_of hInvD.depth_reg
  · -- the merge's index `phi` takes `%inc208.i` on the same edge
    exact stringCleanupKIncoming_at
  · -- the two-entry advance, at the word `if.end207.i` wrote
    exact LeanLLVM.evalOperand_reg_of hinc208
  · -- the index advanced
    omega
  · rw [hnepv]
    exact hk2cap
  · exact hInvD.depth_cap
  · exact hInvD.sp_le_wlen
  · -- the price: the entry term alone pays it, and the byte term is a `Nat`, so
    -- no `entryPos` monotonicity and no terminal-index law is read
    show 15 + 2 ≤ stage2EntryAllowance * (C.k + 2 - C.k) +
      stage2ByteAllowance * (entryPos G (C.k + 2) - entryPos G C.k)
    simp only [stage2EntryAllowance, stage2ByteAllowance]
    omega

/-! ### Axiom footprints

Each pin states the footprint the lemma actually has.  The composed segment and the
arm cost `Propext`, `Classical.choice` and `Quot.sound`: the composition selects
through `s2AfterValueContract.resolves`' disjunction and `walkBitVec1_zero_or_one`'s,
which is the choice `walkEvalICmp_ult_one_iff` alone does not carry. -/

/-- info: 'LeanLLVM.Refinement.WalkScope.stringPath_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stringPath_seg

/--
info: 'LeanLLVM.Refinement.WalkScope.WalkDispatchResult.ofStringMerge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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
