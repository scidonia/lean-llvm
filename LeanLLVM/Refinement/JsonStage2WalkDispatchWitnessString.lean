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
`sw_bb202_i_at`, `NodeBlock31_at`, `LeafBlock29_at`, `if_else285_i_at`).  Three
remain: `if_end256_i` and `if_then328_i` take an explicit `s₁` and can be exposed
the same way, and `z_arena_reserve_exit`'s target depends on the callee's
`CallOutcome`, so its exposure needs that outcome as a named parameter.

**The residue: four fields, not eight links.**  With the states nameable, every
link's hypotheses are the head bundle's fields, `WalkInv`'s clauses, the step's own
predecessor, or a `def`'d state's cells — except for four facts, each of which is
named here with the producer that will retire it:

* **`z_arena_reserve_exit`'s witness** — one field, not six:
  `∀ r, stage2Calls … "s2_string_body" ⟨the eight arguments⟩ s₉.mem s₉.next = some r
  → hframe ∧ howned ∧ hlog ∧ hev ∧ hstTy ∧ hstSt`, all at `r.mem` and the target
  carry.  Producer: `s2StringBodyFoot_frame_walkWide`
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

**The fifteen-block segment is still a supplied field of this bundle, not a
composition.**  The link that blocks the composition is
`WalkLink.z_arena_reserve_exit` (position 9): its hypotheses include register
bindings that neither `WalkInv` carries nor any block of the chain binds
(`%arrayidx10.i`, `%c.i`, `%xp`, `%nxp` — the first is bound by the *header*,
which is where the loop's own `%idxprom.i` is read, and the rest are the
program's parameters and the token record's pointer), and six memory-class
hypotheses (`hframe`, `howned`, `hlog`, `hev`, `hstTy`, `hstSt`) whose bridge
from `s2StringBodyFoot` to `walkWide` is not a lemma of this layer.  Its `%xj.i`
is the staging's address, `G.next0 + 12`; an earlier statement of the link had
`+ 16`, where the string body's spacing clause is false, and that is repaired at
the link.  Composing the
other fourteen links would still leave a link at the seam, so the bundle takes
the segment whole, at its count, with the endpoint's block, index and
predecessor as fields.

**What the arm reads.**  `WalkDispatchResult.ofStringMerge` reads six of the
bundle's fields: the segment, its endpoint's block, index and predecessor, G9's two
endpoint cells, and G2's count test (`hcount`, without which there is no
`k2 ≤ nepv.toNat` for the merge's `hcap`).  G1 and G3–G8 are **not** read by the
arm.  They are the premise set a composition needs — the fifteen links' hypotheses,
grouped and stated at the head where they are true of the run — so they are the
target of the producer that would retire the supplied segment, and a refactor that
finds them unread and deletes them would delete that target.

**The blockers, named.**  The link at position 9 needs four things this layer does
not carry: a producer of `s2StringBodyPre` at the call site (no staging theorem for
the string body's argument list exists in the tree); the allocator-cursor pin
`C.alen ≤ G.ndst0 + ix.toNat` as a fact about the *call's* state rather than the
loop head's (`pending = none` at a head, so the clause is not invariant-carried);
the two frame lemmas that would carry `s2StringBody_framed`'s
`s2StringBodyFoot` to `walkWide` — one for the frame and one for the presence list
— which are absent, so the link's `hframe`/`howned`/`hlog`/`hev`/`hstTy`/`hstSt`
are supplied at the link rather than derived; and the `RegionsApart` instances
`s2StringBodyPre` asks for, read off the staging's separation, which no lemma
instantiates at the call's argument list.  Its other blocker is a register set:
`walkStaticRegs` omits `%c.i`, `%xp`, `%nxp` and `%arrayidx10.i`, which the link
takes as hypotheses, and adding them to the carrier is the measured 39-site
`WalkInv`-vocabulary change that `WalkMergeCells` and the continuing bundle's two
cursor cells would need as well — not a new idea, and the change that would turn
four of the supplied facts below into produced ones.

The link as written is moreover **unsatisfiable**, independently of those
obstacles: its `hxj` states `%xj.i = G.next0 + 16` while `walkStaticRegs` fixes the
register at `G.next0 + 12`, and `s2StringBodyPre`'s `RegionsApart xj 8 outn 8` fails
at `+ 16` against `%outn.i = G.next0 + 20`.  The census row that calls the link
proved (`JsonStage2WalkScope`) records a proof, not an inhabitant.

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

The segment is a field here — see the module header: the composition is what is
missing, and the link that blocks it is `WalkLink.z_arena_reserve_exit`. -/
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
  /-- **G9 — the segment and the merge's cells.**  The path is supplied whole
  (the module header names the blocking link), and with it the endpoint's block,
  index and predecessor.  The two cells are the merge's on the `if.else334.i`
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
`HstringFacts.seg`, whose composition is the open item the module header names
(`WalkLink.z_arena_reserve_exit`); this lemma is the shape a consumer reads, so
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

end WalkScope

end LeanLLVM.Refinement
