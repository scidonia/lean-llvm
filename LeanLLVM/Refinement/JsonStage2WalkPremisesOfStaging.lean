/-
# The walk's premises, from the staging

`WalkPremises` (`JsonStage2WalkAssembly`) had no producer: its two conjuncts — the empty
stream's flush and the loop's step — were stated and never applied, so
`stage2WalkCompletes_of_premises` and `stage2WalkObligation_of_premises` and the
`Stage2WalkObligation` they conclude were unapplied too.  This module builds the premise
from the record and the adapter's staging: the geometry and the staging are the two
constructions (`walkGeom_at_pre`, `walkStage_at_pre`), the seed's prefix and the
invariant at the loop head are theorems at them (`walkSeedPrefix_entry_geometry`,
`walkSeedInvariant_geometry`), and the two remaining conjuncts — the flush and the loop's
step — are composed here from the steps the layer already states.

## What is composed, and what is supplied

* **The flush**: `walkFlushSteps12`'s two steps, the refusal copy
  (`walkIfThenBlock_denote_named` at the state those two leave) and the return
  (`walkReturn_at`), composed by `WalkFlushAt.ofRun`.  Every read the copy takes is a
  word the staging fixes: the log's arena cursor and its event cursor
  (`walkEntryMemAt_alen`, `walkEntryMemAt_len` — `walkEntryMem_alen`'s and
  `walkEntryMem_len`'s twins at the adapter's own fold), and the refusal offset the
  flush block itself stores.  So the arm needs no hypothesis beside the staging.
* **The seed's prefix and the invariant at the loop head** are
  `walkSeedPrefix_entry_geometry` and `walkSeedInvariant_geometry`, applied at the
  constructed pair.  `WalkPremises` states both at the record's numbers while those two
  lemmas read `WalkStage`'s fields, so the staging is built by
  `walkStage_at_pre_fields` — `walkStage_at_pre`'s construction with the fields named.
* **The loop's step** is `walkLoopStep_of_staging`: `walkLoopStepThree_of_dispatchResult`
  (`JsonStage2WalkDispatchThreeOfRun`) at the dispatch's result, the finalisation's two
  terminal *posts* and the merge's count.  The result is the `merge` arm in both branches:
  where an entry is left, from whichever class the continuing premise names —
  `walkDispatch_at_continue_cells` for the whitespace bundle, `WalkDispatchResult.ofStringMerge`
  for the two-entry one; and from the last entry's bundle where it is not
  (`WalkDispatchResult.ofHlastMerge`).  The posts are `WalkLoopEnd.merge`/`.refuse`'s,
  which produce `WalkTargetPost` from the word bundles and the state's own cells.
* **The loop's post** is `stage2Post_of_staging_loop`: the seed's prefix, the invariant
  and `walkLoopFinishesThree`'s triple, which names the returned verdict and memory, and
  the boundary at that memory is the post.

Three groups are premises, one per obstruction, and each is a bundle rather than a field
per fact:

| premise | what it is | why it is not derived |
|---|---|---|
| `WalkContinueFacts` | the **class** of the continuing entry at every head state with an entry left (`HcontCase`: `ws` = `HcontFacts`, `cleanup` = `HcontCleanupFacts`, `twoEntry` = `HstringFacts`) | each class's bundle is a fact about the token (`walkRevolutionMergeSegWs`'s own for `ws`, `walkRevolutionMergeSeg`'s for `cleanup`), and the class is the head's byte and the byte before the entry's end; the split is a value so the question is asked once |
| `WalkLoopEnd` | the last entry's bundle, the two terminal blocks' *words*, and the merge's `%nep` value | the bundle is supplied at the last-entry head states (`HlastFacts`), the words at the states the dispatch reaches (`WalkMergeWords`, `WalkRefuseWords`), and `%nep` is not a `WalkInv` clause.  The *runs* are proved, not supplied: `WalkLoopEnd.merge`/`.refuse` compose them from `JsonStage2WalkTargetPost`'s four routes |
| `WalkStringResidue` | the two-entry token's path's residue at every head state: the two address widths the staging does not state, the string body's answer, the decoded length and its bound, the log's base word, the strict event count and the event cursor's signed bound (`HstringResidue`, `JsonStage2WalkDispatchWitnessString`) | each field is a helper contract's output or a fact about the input, and the module that composes the path names each one's producer at the field; `stringPath_seg` is the theorem from them.  The static carrier names `%c.i`, `%z`, `%xp` and `%nxp` and `WalkIter` names `%arrayidx10.i`, so the residue carries no register and no memory clause of the body |

The terminal runs are read at the states the dispatch's outcomes reach rather than at the
loop head, so the head-level `%z`/`%s` group this module used to carry is gone with the
route that needed it: the copy's two pointer registers are the terminal states' own.

## When this module's claims are checked

`LeanLLVM.lean` is the default target's manifest, and a module it does not import is
compiled by no default build — its own `lake build` succeeds on a module nothing consumes.
The chain's last modules sat outside that manifest while they were being written, so a
green there was the green of never having been built.  **A theorem is green when the
default target compiles it, not when its own module does.**  This module and the twelve
below it (`HeadChainA`/`C`/`Scan`, `FinishPath`, `PrefixCount`, `DispatchWitnessHlast`,
`DispatchWitnessString`, `RevolutionPrefix`, `Revolution`, `HcontFactsOfStaging`,
`ExitProducer`, `ArenaWord`, `TargetPost`, `FlushPost`) are imported at the end of
`LeanLLVM.lean` for that reason; `TargetPost` is also this module's own import, because
the terminal posts it proves are what `WalkLoopEnd.merge`/`.refuse` compose.
-/

import LeanLLVM.Refinement.JsonStage2WalkExitProducer
import LeanLLVM.Refinement.JsonStage2WalkLoopStepOutcome
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkRevolution
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg
import LeanLLVM.Refinement.JsonStage2WalkSeedAtEntry
import LeanLLVM.Refinement.JsonStage2WalkTargetPost

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing entry's bundle, and the merge's cells -/

/-- **The continuing entry's whitespace facts.**  `walkRevolutionMergeSegWs`'s own bundle
(`HcontFacts`) as a `∀`-producer: the statement the one-entry arm's dispatch needs is
stated per head state, and this is the function that hands it one.

`HcontFacts` describes the path whose byte before the entry's end is **whitespace**: the
skip runs, the token ends at the first whitespace byte `k`, and the extra-token scan runs
`[k, v)` with `k < v`, which is the `heicd` the bundle carries.  Its merge index is
`C.k + 1`, the header's own increment. -/
abbrev WalkContinueWsFacts {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontFacts G C s

/-- **The continuing entry's facts, as the class the token belongs to.**  Two of the
dispatch's arms describe a continuing entry — one with an entry left after it:

* the token ends **inside** its entry and the merge selects `C.k + 1`, which is
  `HcontFacts` (the whitespace class: the skip runs to `k` and the scan runs `[k, v)`) or,
  when the byte before the entry's end is not whitespace, `HcontCleanupFacts` (the
  scan-free class: the token ends at the entry's end and the walk leaves for `if.end473.i`
  without a scan);
* the token is a **standalone string**, whose opener and closer are two entries, so the
  merge selects `%inc208.i = C.k + 2`, which is `HstringFacts`
  (`JsonStage2WalkDispatchWitnessString`).

**These are not a partition, and the docstring must not be read as one.**  The head's
switch (`NodeBlock21` and the pivots below it) has further arms — the numeral token
through `num_fast_el1`, the scalar through `od_scalar_value`, the container openers —
and each of those is a class this inductive does not yet have an arm for.  What the type
provides is the place to put them: a producer that knows the head's byte answers with one
arm, and a new class is a new constructor rather than a re-shaping of every consumer.

The case is a value and not a second conjoined premise.  Two premises would be jointly
uninhabited at exactly the input the walk handles: at `C.k = 0`, `G.nep = 2` the head's
test `0 + 1 < 2` is true, so the continuing branch runs — but the merge's index is `2`,
so a bundle whose index is `C.k + 1` and whose scan runs `[k, v)` with `k < v` has
nothing to describe there.  The class question therefore has to be answered where the
producer knows the answer (the head's byte), and this is where it is answered.

**What the classification still is.**  The case does not classify the dispatch's outcome:
each arm builds the same `merge` result, and `WalkDispatchResult.toOutcome` splits it on
the merge's own test (`%k.2.i < %nep`).  So the standalone string falls out as a `finish`
with no hypothesis about `C.k + 1`, which is the case `standaloneString_finish`
(`JsonStage2WalkDispatchThreeOfRun`) states.

**The scan-free class is the third arm, and it is landed.**  On the arm whose byte before
the entry's end is *not* whitespace the token ends at the entry's end, so `%ee.1.i` *is*
`%cond350.i`, the scan's guard is `v < v`, and the walk leaves for `if.end473.i` without
entering the scan (`contEntry_scan_empty`, `JsonStage2WalkRevolutionPrefix`; `WalkLocal` at
`land.rhs457.i` carries the `ScanEmpty` disjunct, so the step is takeable).
`HcontCleanupFacts` (`JsonStage2WalkRevolution`) is that sibling bundle: its segment is
`hcontPrefixCleanupSeg`'s twenty links plus the merge's one, its cells are
`walkRevolutionMergeSeg`'s, and its price has no byte term — `21 + 2 ≤ 32·Δk`. -/
abbrev WalkContinueFacts {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontCase G C s

/-! ### The head state's two register cells are not premises

`%inc.i` and `%nep` are `WalkInv` clauses now, so the pair the continuing entry's
path reads at the merge is a theorem rather than a supplied bundle: `%inc.i` is
`WalkInv.inc_reg` (`ofNat 64 (C.k + 1)` at every block — the back edge leaves the
carry and the register alone, and the header's pass moves both together) and
`%nep` is one of `walkStaticRegs`' pairs, read by `WalkInv.regs`.
`mergeHeadCells` and its `∀`-form `walkHeadCells` are
`JsonStage2WalkRevolutionSeg`'s, and the bridge below takes the continuing
entry's bundle alone. -/

/-- The merge's `phi` for the depth, read off the block's incoming list. -/
theorem cleanupSpIncoming_at :
    phiIncoming "if.end473.i" cleanupSpIncoming = some (Operand.reg "%sp.i.0248") := by
  decide

/-- The merge's `phi` for the index, read off the block's incoming list. -/
theorem cleanupKIncoming_at :
    phiIncoming "if.end473.i" cleanupKIncoming = some (Operand.reg "%inc.i") := by
  decide

/-- **`WalkDispatch`, from the continuing entry's premise.**  `walkDispatch_at_continue_cells_ws`
(`JsonStage2WalkRevolutionSeg`) at each head state the premise names: the whitespace arm's
segment, its endpoint and the merge's three cells come from that module's composition, so
nothing is assumed about a segment the producer did not build.  The conclusion is
`WalkDispatch`'s body, so this is the bridge from the per-state form to the quantified one.

The scan-free arm's bridge is `walkDispatch_of_continue_cells`, which reads
`HcontCleanupFacts`' `∀`-form: the two arms have different bundles, so each has its own
bridge over the premise that supplies it. -/
theorem walkDispatch_of_continue {m0 : Mem} {G : WalkGeom m0}
    (hcont : WalkContinueWsFacts G) :
    WalkDispatch (stage2Calls stage2SubCalls) G := by
  intro C s hInv hhead hk
  exact walkDispatch_at_continue_cells_ws C s hInv hhead hk (hcont C s hInv hhead hk)

/-! ### The finalisation's terminal runs and the loop's step -/

/-- **The last entry's facts, the finalisation's words, and the merge's count**, at
every state each is read at.  `facts` is the last entry's bundle; `mergeWords` and
`refuseWords` are the three facts no clause carries, one bundle per terminal entry
block; and `nepBound` is the merge's `%nep` value, inside the stream.

The terminal post is not a field: `WalkLoopEnd.merge` and `WalkLoopEnd.refuse` produce it
from the bundles and the state's own cells, and their proofs are the four terminal runs
of `JsonStage2WalkTargetPost`.  So what this structure *supplies* is the words, and what
the layer *proves* is the run and the boundary at its memory.

The three facts, and why they are not clauses:

* `%4 = n`.  `%4` is loaded once by `entry` from `%n2.i = %s + 8` and no block rebinds
  it, but it is not in `walkStaticNames`, so no `WalkInv` clause names it.  Its producer
  is the seed's register carrier (`walkSeedFinalEnv_regs`); adding `"%4"` to
  `walkStaticNames` would make it derivable, and that edit is in the
  twenty-one-megabyte `JsonStage2WalkScope`.
* the merge's root-done word.  `WalkInv.owned` deliberately omits the four `alloca`
  slots, so the root slot's presence is in no clause; its producer is a presence clause
  on `WalkInv` transported link by link.
* R0's refusal word at `if.then`.  `WalkInv.eoff_le` bounds the carry's `eoff` but the
  bytes at `%e + 8` are the *previous* link's store, and `WalkSegment` keeps no memory;
  a memory-carrying refusal segment would produce it.

The log's arena word and the finalisation's eight carrier registers are the fourth and
fifth supplied facts (`WalkMergeWords.log`, `WalkMergeWords.env`), with the write-back
block and the seed's environment as their producers. -/
structure WalkLoopEnd {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The last entry's facts, at every head state the merge's test sends to the exit. -/
  facts : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) → HlastFacts G C s
  /-- **The merge's words**, at every state a dispatch reaches at `cleanup478.i`. -/
  mergeWords : ∀ (Cd : WalkCarry G) (sd : State), WalkInv G Cd sd →
    Cd.block = "cleanup478.i" → WalkMergeWords G Cd sd
  /-- **The refusal copy's words**, at every state a refusal reaches at `if.then`. -/
  refuseWords : ∀ (Cd : WalkCarry G) (sd : State), WalkInv G Cd sd →
    Cd.block = "if.then" → WalkRefuseWords G Cd sd
  /-- **The merge's `%nep` value is inside the stream**: the last entry's price is stated
  against the credit its index consumed, and this is what makes that credit the
  potential's. -/
  nepBound : ∀ (Cd : WalkCarry G) (sd : State) (nepv : BitVec 64),
    WalkInv G Cd sd → Cd.block = "cleanup478.i" →
    lookupName sd.env "%nep" = some (.int 64 nepv) → nepv.toNat ≤ G.nep

/-- **The merge's terminal post, from the merge's words and its cells.**  The depth's
zero test and the root-done test select the finalisation's route, and the route's run is
`JsonStage2WalkTargetPost`'s.  `%nep`'s value is the outcome's (`hnep`) and the staging's
(`WalkFinalEnv`'s last field); the two agree because the staging fixes the parameter, and
that agreement is what turns the outcome's `hterm` into the merge's. -/
theorem WalkLoopEnd.merge {m0 : Mem} {G : WalkGeom m0} (h : WalkLoopEnd G)
    (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
    (spOp kOp : Operand) (nepv : BitVec 64)
    (hInv : WalkInv G Cd sd) (hblk : Cd.block = "cleanup478.i")
    (hpre : sd.pre = some prev)
    (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
    (hspv : evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming prev cleanupKIncoming = some kOp)
    (hkv : evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName sd.env "%nep" = some (.int 64 nepv)) (hterm : k2 = nepv.toNat) :
    WalkTargetPost (stage2Calls stage2SubCalls) G Cd sd := by
  obtain ⟨hwenv, hwlog, hw4, hwroot⟩ := h.mergeWords Cd sd hInv hblk
  exact walkFinishPost_merge G Cd sd hInv
    hblk hpre hsp hspv hk hkv hnep hterm
    ⟨hwenv, hwlog, hw4, hwroot⟩

/-- **The refusal copy's terminal post, from the copy's words.**  R0: the state is at
`if.then` already, so the post is the copy's two steps at the word the previous link
stored. -/
theorem WalkLoopEnd.refuse {m0 : Mem} {G : WalkGeom m0} (h : WalkLoopEnd G)
    (Cd : WalkCarry G) (sd : State) (hInv : WalkInv G Cd sd)
    (hblk : Cd.block = "if.then") :
    WalkTargetPost (stage2Calls stage2SubCalls) G Cd sd :=
  walkFinishPost_refuseOfWords G Cd sd hInv hblk
    (h.refuseWords Cd sd hInv hblk)

/-- **The loop's step, from the three bundles.**  `walkLoopStepThree_of_dispatchResult`
(`JsonStage2WalkDispatchThreeOfRun`) asks for the dispatch's result at every head state,
the finalisation's two terminal runs and the merge's count.  The result is the `merge` arm
in both branches: where an entry is left, from whichever class the continuing premise names
— `walkDispatch_at_continue_cells`' own evidence for the whitespace token, whose index and
depth are its fields, and `HstringFacts` for the standalone string; and from the last entry's
bundle (`WalkDispatchResult.ofHlastMerge`) where it is not.  The runs and the count are
`WalkLoopEnd`'s.

**What the branch on `C.k + 1 < G.nep` now is, and what it is not.**  It selects *which
bundle describes the head state* — the continuing entry's or the last entry's — because
the two bundles are the input's facts about those two states and `HlastFacts` is
uninhabited elsewhere.  It no longer decides the dispatch's outcome: both branches build
the same `merge` arm, and `WalkDispatchResult.toOutcome` classifies it by the merge's index
against `%nep`.  So the `finish` outcome is reachable from either branch, and the
standalone string's `finish` is what `standaloneString_finish` states.

**The continuing branch is a class, and the two-entry class is an arm.**  The continuing
branch asks which walk consumes the entry: `HcontFacts` (a token that ends inside its
entry, merge index `C.k + 1`) or `HstringFacts` (a standalone string, opener and closer,
merge index `C.k + 2`).  At `C.k = 0`, `G.nep = 2` it is the second arm, so the branch is
no longer vacuous: it is a premise with a name, and the arm that consumes it is
`WalkDispatchResult.ofStringMerge` (`JsonStage2WalkDispatchWitnessString`), which composes
the fifteen-block segment from `HstringResidue` — the residue premise below.  The segment
is no longer a supplied field of the bundle; what is supplied is the residue, one bank of
facts per head state, and each of its fields names its producer in that module. -/
theorem walkLoopStep_of_staging {m0 : Mem} {G : WalkGeom m0}
    (hcont : WalkContinueFacts G) (hend : WalkLoopEnd G)
    (hres : ∀ {m0 : Mem} (G : WalkGeom m0), WalkStringResidue G) :
    WalkLoopStepThree (stage2Calls stage2SubCalls) G 27 :=
  walkLoopStepThree_of_dispatchResult (Nat.le_refl 27)
    (fun C s hInv hhead => by
      by_cases hk : C.k + 1 < G.nep
      · rcases hcont C s hInv hhead hk with hws | hcln | hstr
        · obtain ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblk, hkC, hpre, hsp,
            hspv, hkOp, hk2, hnepv, hbelow, _hnep, hadvance, hspcap, hspw, hprice⟩ :=
            walkDispatch_at_continue_cells_ws C s hInv hhead hk hws
          exact WalkDispatchResult.merge Cd sd p spv k2 prev spOp kOp nepv seg hblk hkC
            hpre hsp hspv hkOp hk2 hnepv hadvance (le_of_lt hbelow) hspcap hspw hprice
        · obtain ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblk, hkC, hpre, hsp,
            hspv, hkOp, hk2, hnepv, hbelow, _hnep, hadvance, hspcap, hspw, hprice⟩ :=
            walkDispatch_at_continue_cells C s hInv hhead hk hcln
          exact WalkDispatchResult.merge Cd sd p spv k2 prev spOp kOp nepv seg hblk hkC
            hpre hsp hspv hkOp hk2 hnepv hadvance (le_of_lt hbelow) hspcap hspw hprice
        · exact WalkDispatchResult.ofStringMerge G C s hhead hInv hstr
            (hres G C s hInv hhead hk hstr)
      · exact WalkDispatchResult.ofHlastMerge G C s hInv hhead
          (hend.facts C s hInv hhead hk))
    (fun Cd sd p spv k2 prev spOp kOp nepv hInv hblk hpre hsp hspv hkOp hk2 hnepv hterm =>
      hend.merge Cd sd p spv k2 prev spOp kOp nepv hInv hblk hpre hsp hspv hkOp hk2 hnepv
        hterm)
    (fun Cd sd hInv hblk => hend.refuse Cd sd hInv hblk)
    (fun nepv Cd sd hInv hblk hnep => hend.nepBound Cd sd nepv hInv hblk hnep)

/-! ### The empty entry stream's flush, from the staging -/

/-- A store leaves the block: `walkSetMem` changes the memory and nothing else. -/
theorem walkSetMem_pc (s : State) (m : Mem) : (walkSetMem s m).pc = s.pc := rfl

/-- Naming a state at an environment leaves the block. -/
theorem stateAt_pc (env : Env) (s : State) : (stateAt env s).pc = s.pc := rfl

/-- **The refusal copy's state is at its input's block.**  The lemma is stated at the
general shape — the state and its memory as variables — because that shape is free and
the instance is not: the copy's state is a three-deep nest of `writeBytes`, and a `rfl`
at a *named* state's `.pc` exceeds 200 000 heartbeats deterministically (a `whnf`
timeout), while the same fact with the memory a variable is instant.  At a term whose
head is a variable the projection needs one unfold of each layer; at a named one it
unfolds the three writes and their byte lists at every position. -/
theorem walkIfThenBlockState_pc (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) : (walkIfThenBlockState env nd nv err e A L E s).pc = s.pc := by
  simp only [walkIfThenBlockState, stateAt_pc, walkSetMem_pc]

/-- The bytes written at an address are read back at it, at any width that spells
their length. -/
theorem readBytes_writeBytes_len {m : Mem} {bs : List UInt8} {a n : Nat}
    (h : n = bs.length) : readBytes (writeBytes m a bs) a n = some bs := by
  subst h
  exact readBytes_writeBytes_same m bs

/-- **A read inside the log's sixty-four bytes passes the entry run's later writes.**
The adapter's memory is the second segment's and the third's and the fourth's; this is
`walkEntryMem_read_out` with the header's store absent, which is the only difference
between the two folds. -/
theorem walkEntryMemAt_read_out {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a len : Nat} (hz0 : S.z ≤ a) (hz1 : a + len ≤ S.z + 64) :
    readBytes (walkEntryMemAt G S) a len =
      readBytes
        (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
          G.evcap
          (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
            ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)) a len := by
  obtain ⟨hcz, hzn⟩ := walkStage_log_sep G S
  show readBytes
      (walkSeg4PostMem (G.next0 + 8) (G.next0 + 12)
        (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
          (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
            G.evcap
            (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
              ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)))) a len = _
  rw [readBytes_walkSeg4PostMem_out (root := G.next0 + 8) (xj := G.next0 + 12)
    (by left; omega) (by left; omega)]
  rw [readBytes_walkSeg3PostMem_out (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
    (eAddr := S.e) (cAddr := S.c) ?_]
  intro st hst
  obtain ⟨hlo, hhi⟩ := walkSeg3Stores_bounds G.b G.n G.ep G.nep S.e S.c st hst
  rcases hcz with h | h <;> omega

/-- **The log's arena cursor at the adapter's memory.**  `walkEntryMem_alen`'s twin:
the read passes the third and fourth segments because it lies inside the log, and the
second segment is where the initialisation wrote the staged cursor. -/
theorem walkEntryMemAt_alen {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMemAt G S) (S.z + 48) 8 = some (wordBytes 8 G.ndst0) := by
  have h := walkEntryMemAt_read_out G S (a := S.z + 48) (len := 8) (by omega) (by omega)
  rw [h]
  have h2 := walkSeg2PostMem_alen (m := m0) (sAddr := S.s) (b := G.b) (ep := G.ep)
    (zAddr := S.z) (nep := G.nep) (xp := G.xp) (nxp := G.nxp) (dst := G.dst)
    (v1 := G.ndst0) (dstcap := G.dstcap) (ev := G.ev) (v2 := G.nev0) (evcap := G.evcap)
    (n := BitVec.ofNat 64 G.n) (nb := (BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6)
  simpa only [woff_48] using h2

/-- **The log's event cursor at the adapter's memory.**  `walkEntryMem_len`'s twin. -/
theorem walkEntryMemAt_len {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMemAt G S) (S.z + 8) 8 = some (wordBytes 8 G.nev0) := by
  have h := walkEntryMemAt_read_out G S (a := S.z + 8) (len := 8) (by omega) (by omega)
  rw [h]
  have h2 := walkSeg2PostMem_len (m := m0) (sAddr := S.s) (b := G.b) (ep := G.ep)
    (zAddr := S.z) (nep := G.nep) (xp := G.xp) (nxp := G.nxp) (dst := G.dst)
    (v1 := G.ndst0) (dstcap := G.dstcap) (ev := G.ev) (v2 := G.nev0) (evcap := G.evcap)
    (n := BitVec.ofNat 64 G.n) (nb := (BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6)
  simpa only [woff_8] using h2

/-- **The empty entry stream's flush, at the staging.**  At `nep = 0` the entry block
takes its zero arm, the flush block runs and the refusal copy writes the record's
three slots; `walkReturn_at` then returns the arm's literal zero.  The four steps are
`walkFlushSteps12`'s two, `walkIfThenBlock_denote_named`'s copy and `walkReturn_at`'s
return, and `WalkFlushAt.ofRun` composes them inside the finalisation allowance.

Every read the copy takes is a word the staging fixes: the log's arena cursor and its
event length (`walkEntryMemAt_alen`, `walkEntryMemAt_len`), and the refusal offset the
flush block's own store writes.  The three disjointness premises are the staged objects' — the log beside
the error record, and the two cursor slots beside it — so the arm needs nothing the
record does not supply. -/
theorem walkFlushAt_of_staging {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a13 : List Value} {next d : Nat}
    (h13 : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : next = G.next0) (hzero : G.nep = 0) :
    ∃ v0 : Value,
      WalkFlushAt (stage2Calls stage2SubCalls) v0 m0 next a13 G.nep d
        S.c S.ctype S.cst S.tok S.s S.z S.e := by
  obtain ⟨s₁, s₂, h1, h2, hpc2, hxj, hrd, halen, hlen, hc, hctp, hcst, hnd, hnev, he,
    herr, hmem2, henv2⟩ := walkFlushSteps12 (mem := m0) (d := d) G S hzero
  -- the two slots the copy reads, at the record's own offsets
  have hz48 : S.z + woff 48 = S.z + 48 := by rw [woff_48]
  have hz8 : S.z + woff 8 = S.z + 8 := by rw [woff_8]
  -- widths: the three staged words the copy reads
  have hn64 : G.n < 2 ^ 64 := by
    have h2' := G.maxDoc
    simp only [stage2MaxDocument] at h2'
    omega
  have hndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  have hnev0 : G.nev0 < 2 ^ 64 := by
    have hroom := G.evRoom
    have hcap := G.evcapLt
    omega
  -- the staged objects' separation, at the extents the stores lie in
  have hEZ : S.e + 24 ≤ S.z ∨ S.z + 64 ≤ S.e := by
    have h := staged_pair (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
      (xp := G.xp) (nxp := G.nxp) (dst := G.dst) (ndst0 := G.ndst0) (ev := G.ev)
      (evcap := G.evcap) (ndst := G.ndst) (nev := G.nev) (err := G.err)
      (c := S.c) (ctype := S.ctype) (cst := S.cst) (tok := S.tok) (sv := S.s)
      (z := S.z) (e := S.e) S.separate
      (r := (S.z, stage2LogExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
      (by
        intro hh
        have h2' : stage2LogExtent = stage2ErrorExtent := congrArg Prod.snd hh
        exact absurd h2' (by decide))
    have h' : S.z + 64 ≤ S.e ∨ S.e + 24 ≤ S.z := h
    omega
  have hEd : G.ndst + 8 ≤ S.e + 8 ∨ S.e + 8 + 8 ≤ G.ndst := by
    have h := walkRegion_against_writes S (r := (G.ndst, 8)) (by simp [stage2Regions])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2StagedWrites])
    have h' : G.ndst + 8 ≤ S.e ∨ S.e + 24 ≤ G.ndst := h
    omega
  have hEn : G.nev + 8 ≤ S.e + 8 ∨ S.e + 8 + 8 ≤ G.nev := by
    have h := walkRegion_against_writes S (r := (G.nev, 8)) (by simp [stage2Regions])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2StagedWrites])
    have h' : G.nev + 8 ≤ S.e ∨ S.e + 24 ≤ G.nev := h
    omega
  have hZd : G.ndst + 8 ≤ S.z + woff 8 ∨ S.z + woff 8 + 8 ≤ G.ndst := by
    have h := walkRegion_against_writes S (r := (G.ndst, 8)) (by simp [stage2Regions])
      (q := (S.z, stage2LogExtent)) (by simp [stage2StagedWrites])
    have h' : G.ndst + 8 ≤ S.z ∨ S.z + 64 ≤ G.ndst := h
    omega
  -- the copy's three reads, at the memory the flush block leaves
  have hmem : s₂.mem = writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n) := hmem2
  -- the return's two other registers: the entry environment's, untouched on the arm
  have hz₂ : lookupName s₂.env "%z" = some (.ptr S.z) := by
    rw [henv2]
    simp [walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells,
      lookupName_cons_ne, walkEntryState_env]
  have hs₂ : lookupName s₂.env "%s" = some (.ptr S.s) := by
    rw [henv2]
    simp [walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells,
      lookupName_cons_ne, walkEntryState_env]
  have hA : readBytes s₂.mem (S.z + woff 48) 8 =
      some (natToBytes (BitVec.ofNat 64 G.ndst0).toNat 8) := by
    rw [hmem, hz48]
    have hout : S.z + 48 + 8 ≤ S.e + 8 ∨ S.e + 8 + (wordBytes 8 G.n).length ≤ S.z + 48 := by
      have hl : (wordBytes 8 G.n).length = 8 := by simp [wordBytes, natToBytes_length]
      omega
    rw [walkReadBytes_writeBytes_outside (m := walkEntryMemAt G S) (v := wordBytes 8 G.n)
      (start := S.e + 8) (addr := S.z + 48) (n := 8) hout]
    rw [walkEntryMemAt_alen G S]
    rw [show (BitVec.ofNat 64 G.ndst0).toNat = G.ndst0 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hndst0]]
    rfl
  have hL : readBytes s₂.mem (S.z + woff 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.nev0).toNat 8) := by
    rw [hmem, hz8]
    have hout : S.z + 8 + 8 ≤ S.e + 8 ∨ S.e + 8 + (wordBytes 8 G.n).length ≤ S.z + 8 := by
      have hl : (wordBytes 8 G.n).length = 8 := by simp [wordBytes, natToBytes_length]
      omega
    rw [walkReadBytes_writeBytes_outside (m := walkEntryMemAt G S) (v := wordBytes 8 G.n)
      (start := S.e + 8) (addr := S.z + 8) (n := 8) hout]
    rw [walkEntryMemAt_len G S]
    rw [show (BitVec.ofNat 64 G.nev0).toNat = G.nev0 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnev0]]
    rfl
  have hE : readBytes s₂.mem (S.e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.n).toNat 8) := by
    rw [hmem]
    rw [readBytes_writeBytes_len (bs := wordBytes 8 G.n) (n := 8)
      (by simp [wordBytes, natToBytes_length])]
    rw [show (BitVec.ofNat 64 G.n).toNat = G.n by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
    rfl
  -- the copy itself, in its named state
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs s₂ =
      some (walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
        (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂) := by
    have h := walkIfThenBlock_denote_named (sub := stage2SubCalls) (env := s₂.env) (s := s₂)
      hxj hrd hcst hctp hc halen hnd hlen hnev he herr hA hL hE hZd hEd hEn
    rwa [stateAt_self] at h
  have hpc₃ : (walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
      (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂).pc
      = s₂.pc := walkIfThenBlockState_pc _ _ _ _ _ _ _ _ _
  obtain ⟨s₃, h3, hpc₃', henv₃, hpre₃⟩ :=
    walkRefusalCopy_at (sub := stage2SubCalls) (s := s₂)
      (s₁ := walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
        (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂)
      hpc2 hden hpc₃
  -- the return, at the refusal arm's literal zero
  have hcells := walkRefusalCopyState_cells s₂.env G.ndst G.nev G.err S.e
    (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂
  have hpre₃' : s₃.pre = some "if.then" := by
    rw [hpre₃, hpc2]
  obtain ⟨s₄, h4⟩ := walkReturn_at (sub := stage2SubCalls) (s := s₃) hpc₃'
    (by rw [henv₃]; exact hcells.1.trans he) (by rw [henv₃]; exact hcells.2.1.trans hz₂)
    (by rw [henv₃]; exact hcells.2.2.trans hs₂) hpre₃' walkIfEnd_refusal_phi rfl
  exact ⟨.int 64 0, WalkFlushAt.ofRun (sub := stage2SubCalls) (v0 := .int 64 0)
    (nep := G.nep) (mem := m0) (next := next) hzero
    (by rw [h13, hnext]; exact h1) h2 h3 h4⟩

/-! ### The staging at the record's own numbers -/

/-- **The adapter's staging, at the record's numbers.**  `walkStage_at_pre` constructs
the `WalkStage` from the staged predicate's witnesses, so its fields *are* the record's
— `c`, `ctype`, `cst`, `tok`, `s`, `z`, `e` and `d`.  That is a fact about the
construction and not about an arbitrary staging, and it is what the flush and the seed
read: `WalkPremises` states both at the record's numbers, while the two lemmas that
produce them are stated at the staging's.

The construction is `walkStage_at_pre`'s, with the fields named; the geometry and the
disjointness are that lemma's own. -/
theorem walkStage_at_pre_fields {args : List Value} {m0 : Mem} {next : Nat}
    {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hpre : Γ_stage2.pre args m0 next)
    (hst : stage2StagedPre args m0 next d c ctype cst tok s z e nkSlot nxpSlot) :
    ∃ (G : WalkGeom m0) (S : WalkStage G), G.next0 = next ∧
      S.c = c ∧ S.ctype = ctype ∧ S.cst = cst ∧ S.tok = tok ∧ S.s = s ∧
      S.z = z ∧ S.e = e ∧ S.d = d ∧
      args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] := by
  obtain ⟨G, hnext, hargs⟩ := walkGeom_at_pre hpre
  obtain ⟨hpres, hd8, b', nw, ep', nepw, xp', nxpw, dst', dstcapw, ndst0', ev', evcapw,
    ndst', nev', err', hargs', hread', hdisj', hndst0w, hwm'⟩ := hst
  obtain ⟨-, -, -, -, -, -, -, -, hndstEq, -, -, -, -⟩ :=
    stage2Args_components hargs hargs'
  have hmod : G.ndst0 % 2 ^ 64 = ndst0' % 2 ^ 64 := by
    have hreadG : readBytes m0 ndst' 8 = some (wordBytes 8 G.ndst0) := by
      rw [← hndstEq]; exact G.ndstRead
    exact wordBytes8_mod_eq (Option.some.inj (hreadG.symm.trans hread'))
  have hGndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  have hrecon := stage2StagedRegions_reconcile hargs hargs' (WalkGeom.n_lt G)
    (WalkGeom.nep_lt G) G.nxpLt G.dstcapLt G.evcapLt hGndst0 hndst0w hmod
    c ctype cst tok s z e nkSlot nxpSlot
  have hdisjG : DisjointRegions
      ((stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
          G.ndst G.nev G.err c ctype cst tok s z e ++ [(d, 8)]) ++
        [(nkSlot, 8), (nxpSlot, 8)]) := by
    rw [← hrecon] at hdisj'
    simpa only [stage2StagedRegions, List.append_assoc] using hdisj'
  refine ⟨G, WalkStage.mk c ctype cst tok s z e nkSlot nxpSlot ?_ hpres d hd8 ?_ ?_,
    hnext, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hargs⟩
  · exact walkDisjoint_drop_member hdisjG
  · have hL : DisjointRegions
        (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
          G.ndst G.nev G.err c ctype cst tok s z e ++
          [(d, 8), (nkSlot, 8), (nxpSlot, 8)]) := by
      simpa only [List.append_assoc, List.singleton_append] using hdisjG
    unfold DisjointRegions at hL
    rw [List.pairwise_append] at hL
    obtain ⟨-, -, hcross⟩ := hL
    exact fun r hr => hcross r hr (d, 8) (by simp)
  · rw [hnext]; exact hwm'

/-! ### The premises, from the record and the staging -/

/-- **`WalkPremises` from the record's staging.**  The two branches are the record's
own: at `G.nep = 0` the entry block's zero arm runs the flush (`walkFlushAt_of_staging`,
which needs nothing the staging does not supply), and with entries left the seed's
prefix and the invariant at the loop head are the two theorems at the constructed pair
(`walkSeedPrefix_entry_geometry`, `walkSeedInvariant_geometry`) and the loop's step is
`walkLoopStep_of_staging` at the three bundles.

The stage is `walkStage_at_pre_fields`', so the flush and the seed are stated at the
record's numbers: those lemmas read `WalkStage`'s fields, `WalkPremises` names the
record's, and the fields' equalities are the construction's.

The three bundles are the premises, one group each: the continuing entry's facts, the last
entry's facts with the exit's tail, and the two-entry token's residue.  The merge's two
register cells are not among them: they are `WalkInv` clauses, and `mergeHeadCells` reads
them at the head state. -/
theorem walkPremises_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkContinueFacts G)
    (hend : ∀ {m0 : Mem} (G : WalkGeom m0), WalkLoopEnd G)
    (hres : ∀ {m0 : Mem} (G : WalkGeom m0), WalkStringResidue G) :
    WalkPremises d c ctype cst tok s z e nkSlot nxpSlot := by
  intro a13 mem next hpre hst
  obtain ⟨G, S, hnext, hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd, hargs⟩ :=
    walkStage_at_pre_fields hpre hst
  refine ⟨mem, G, S, hnext, hargs, ?_⟩
  by_cases hzero : G.nep = 0
  · left
    obtain ⟨v0, hv⟩ := walkFlushAt_of_staging G S hargs hnext.symm hzero
    exact ⟨hzero, v0, by
      simpa only [hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd] using hv⟩
  · right
    have hpos : 0 < G.nep := Nat.pos_of_ne_zero hzero
    refine ⟨hpos, ?_, ?_, ?_⟩
    · -- the seed's three-step prefix to the loop head
      intro n
      have h := walkSeedPrefix_entry_geometry (d := d) G S hargs hnext.symm hpos n
      simpa only [hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd] using h
    · -- the invariant at the loop head
      refine walkSeedInvariant_geometry G S
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
        hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hargs, walkEntryState_env, hSct]
        simp [lookupName]
      · rw [hargs, walkEntryState_env, hScs]
        simp [lookupName]
      · rw [hargs, walkEntryState_env, hSc]
        simp [lookupName]
      · rw [hargs, walkEntryState_env, hSz]
        simp [lookupName]
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
      · exact hnext.symm
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
    · -- the loop's step, from the three bundles
      exact walkLoopStep_of_staging (G := G) (hcont G) (hend G) (hres := hres)

/-! ### The loop's post, from the staging

The `nep > 0` arm owes the record's post, and the post is `stage2Boundary` at the memory
the run returns.  The three facts that produce it are the seed's prefix, the invariant at
the loop head and the loop's step; `walkLoopFinishesThree` turns them into a run with its
verdict, its memory and the boundary there, and `stage2Post_of_completion` carries that
one outcome to every behaviour of the run.

The verdict is the run's and not the arm's: the finalisation decides between `1` and `0`
at the merge's and the copy's tests, and the boundary is read at the memory each route
returns (`JsonStage2WalkTargetPost`).  This is why the post cannot be a fixed verdict at
a fixed memory, and why the terminal vocabulary had to carry both. -/

/-- **The loop's post, at the staging.**  At `nep > 0` the entry block's test sends the
run into the loop; the seed's three steps (`walkSeedPrefix_entry_geometry`), the invariant
at the loop head (`walkSeedInvariant_geometry`), the loop's step and its completion
(`walkLoopFinishesThree` at `F ≤ 27`) give the returned verdict and memory, and the
boundary at that memory is the post. -/
theorem stage2Post_of_staging_loop {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    {a13 : List Value} {mem : Mem} {next : Nat} {G : WalkGeom mem} {S : WalkStage G}
    (hSc : S.c = c) (hSct : S.ctype = ctype) (hScs : S.cst = cst) (hStok : S.tok = tok)
    (hSs : S.s = s) (hSz : S.z = z) (hSe : S.e = e)
    (hargs : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (hpos : 0 < G.nep) {F : Nat}
    (hloop : WalkLoopStepThree (stage2Calls stage2SubCalls) G F) :
    ∀ o, BehFromState (stage2Calls stage2SubCalls) stage2Body
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) o →
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post
        (stage2Args a13 d c ctype cst tok s z e) mem next o := by
  -- the seed's three steps, and the invariant at the loop head
  have hseed : ∀ k, runFuel (stage2Calls stage2SubCalls) (3 + k) stage2Body
      (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
        mem next) =
      runFuel (stage2Calls stage2SubCalls) k stage2Body
        (walkSeedFinalState G S
          (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
            mem next) (entryPos G 0) (entryByte G 0)) :=
    fun k => walkSeedPrefix_entry_geometry G S hargs hnext.symm hpos k
  have hInv : WalkInv G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
          mem next) (entryPos G 0) (entryByte G 0)) := by
    refine walkSeedInvariant_geometry G S
      (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
        mem next) hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hargs, walkEntryState_env, hSct]
      simp [lookupName]
    · rw [hargs, walkEntryState_env, hScs]
      simp [lookupName]
    · rw [hargs, walkEntryState_env, hSc]
      simp [lookupName]
    · rw [hargs, walkEntryState_env, hSz]
      simp [lookupName]
    · rw [hargs, walkEntryState_env]
      simp [lookupName]
    · rw [hargs, walkEntryState_env]
      simp [lookupName]
    · exact hnext.symm
    · rw [hargs, walkEntryState_env]
      simp [lookupName]
  have hk : (walkSeed G S).k < G.nep := by
    show 0 < G.nep
    exact hpos
  obtain ⟨q, v, m, -, hrun, hb⟩ :=
    walkLoopFinishesThree hloop (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
          mem next) (entryPos G 0) (entryByte G 0))
      hInv (walkSeed_block G S) hk
  -- the seed's state is the record's entry state
  have hstate : EntryState stage2Body
      (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e) mem next =
      EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next := by
    rw [hSc, hSct, hScs, hStok, hSs, hSz, hSe]
  have hcom : runFuel (stage2Calls stage2SubCalls) (3 + (q + 2)) stage2Body
      (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
      some (.ret (some (.int 64 v)) m) := by
    rw [← hstate, hseed (q + 2)]
    exact hrun
  have hgood : stage2Post a13 mem next (.ret (some (.int 64 v)) m) := by
    show stage2Boundary a13 mem next m (.int 64 v)
    rw [hargs, ← hnext]
    exact hb
  intro o hb'
  show stage2Post ((stage2Args a13 d c ctype cst tok s z e).take 13) mem next o
  rw [stage2Args_take13 a13 (by rw [hargs]; rfl)]
  exact stage2Post_of_completion hcom hgood o hb'

/-! ### The completion and the walk's obligation

`stage2WalkCompletes_of_premises` and `stage2WalkObligation_of_premises` were stated and
never applied; these are their applications at the premises above.  Nothing new is
proved: the two conditionals' own statements are read at `walkPremises_of_staging`.

The obligation's second argument is the record's post rule, which
`stage2WalkObligation_of_premises` names and this layer does not read: it is the run's
region claim at the outcome, and `stage2Post_of_run` is what produces it from a
`Stage2Run` and a completion.  It is a hypothesis here for the same reason it is one
there — the state's post is not the walk's statement.
-/

/-- **The completion, from the three premises.**  `stage2WalkCompletes_of_premises` at
`walkPremises_of_staging`: the body's run reaches an outcome inside the record's budget
whenever the record's pre and the adapter's staging hold. -/
theorem stage2WalkCompletes_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkContinueFacts G)
    (hend : ∀ {m0 : Mem} (G : WalkGeom m0), WalkLoopEnd G)
    (hres : ∀ {m0 : Mem} (G : WalkGeom m0), WalkStringResidue G) :
    Stage2WalkCompletes d c ctype cst tok s z e nkSlot nxpSlot stage2SubCalls :=
  stage2WalkCompletes_of_premises (walkPremises_of_staging hcont hend hres)

 /-! **The walk's obligation: the completion half here, the post half one module up.**
`Stage2WalkObligation` is `Satisfies` at `Γ_stage2at`, and its two conjuncts are the
completion (`stage2WalkCompletes_of_staging`, above) and the post at every behaviour of
the run.  The post's two arms are the empty entry stream's (`stage2Post_of_staging_flush`,
`JsonStage2WalkFlushPost`) and the loop's (`stage2Post_of_staging_loop`, above), and the
first of those lives above this module: `JsonStage2WalkFlushPost` imports this one, so
the record's obligation is stated there, where both arms are in scope. -/

/-! ### The four premises, and what each one owes

The composition is complete; what remains is one premise per obstruction, and this is
the map.  None of the four is a gap in the composition — each is either a fact about
the input or a named missing preservation lemma.

| premise | status |
|---|---|
| `WalkContinueFacts` | **a class of three arms, each with its own evidence.**  The whitespace arm is `HcontFacts`' supply, in `HlastFacts`' discipline: its producer is `hlastFacts_of_staging`'s twin — the same three sources (the invariant's clauses, the document's content, the staging's addresses) read at the run class's states — and the bundle's fields are the head's byte and its four pivot bits, the entry counts and the default arm's cells, the whitespace run and its stop `k`, the seam's byte, the tail's segment and the scan's landing.  That twin is `hcontFacts_of_staging` (`JsonStage2WalkHcontFactsOfStaging`), and what it takes from its caller is the document's bytes and their classes, the whitespace run (`contWsRun`, planned) with its price, the tail's segment, the scan's landing and its traversal's three hypotheses (`hround`, `hguard`, `hbyte`, supplied unweakened), `htok`, which needs *the extra-token scan preserves a register it does not bind* — a statement a `WalkSegment` cannot carry, because the traversal returns its final state existentially — and the run endpoint's two registers and scan bound, which need the same lemma one segment out.  **The count test's value is `1` here and `0` in `HlastFacts`, and both are right**: the fields are arm-specific — a continuing entry has one after it, so the scan's bound is above its index, while the last entry's is the stream's end.  A docstring that gives either value without its arm reads as a contradiction in the other.  **`hnext` is derived, not supplied**: it follows from `C.k + 1 < G.nep` with the two counts pinned to `%k.0.i249 + 1` and `G.nep` (`cont_ult_one`), and `%inc.i`/`%nep` are clauses (`WalkInv.inc_reg`, `WalkInv.regs`) — so the group is closed.  The scan-free arm is `HcontCleanupFacts` (`JsonStage2WalkRevolution`), whose segment needs no scan, no tail budget and no traversal and whose price has no byte term.  The two-entry arm is `HstringFacts` (`JsonStage2WalkDispatchWitnessString`), whose fifteen-block segment is **supplied rather than composed**: `WalkLink.z_arena_reserve_exit`'s address is now the staging's (it had stated `%xj.i` at `G.next0 + 16`, where the string body's `RegionsApart xj 8 outn 8` is false against `%outn.i = G.next0 + 20`; it is `+ 12` now), but the link still needs the register carriers `walkStaticRegs` omits and the two `s2StringBodyFoot`→`walkWide` frame lemmas, and the string body's call site has no `s2StringBodyPre` producer.  Its other groups come from the same three sources, and its two merge cells are fields at its own endpoint rather than `WalkInv` clauses. |
| `WalkContinueWsFacts` | **the whitespace class's `∀`-form; `walkDispatch_of_continue` reads it.**  Its content is `HcontFacts` at every head state with an entry left, and the dispatch bridge proves `WalkDispatch` from it with `walkDispatch_at_continue_cells_ws` (`JsonStage2WalkRevolutionSeg`), the whitespace arm's own composition.  `hcontFacts_of_staging` produces `HcontFacts` at *one* state, not this `∀` (a `∀` would have to inhabit `HcontFacts` at states whose class is another arm's, which is what the class split exists to avoid), which is why the loop's step calls the per-state dispatch instead.  The scan-free arm's `∀`-form is spelled in `walkDispatch_of_continue_cells` (`JsonStage2WalkRevolutionSeg`), which reads `HcontCleanupFacts` and is the same bridge for that arm.  The pair is kept so `WalkDispatch` keeps its only producer — `WalkDispatchOutcome.ofDispatch` and `WalkDispatch.revolution` consume that predicate — and the bridge is a two-line wrapper over the per-state dispatch, so the two cannot drift. |
| `WalkHeadCells` | **retired: proved, not supplied.**  `mergeHeadCells` (`JsonStage2WalkRevolutionSeg`) produces `MergeHeadCells` from `WalkInv` alone — `%inc.i` is `WalkInv.inc_reg` and `%nep` is one of `walkStaticRegs`' pairs — and `walkHeadCells` is its `∀`-form, which is what the loop's step and `walkDispatch_of_continue` read.  The clause is uniform (`ofNat 64 (C.k + 1)` at every block): the back edge (`walkBack_step`) advances neither `C.k` nor the register, and `whileBody_step` moves both together, so the block-keyed form this row used to propose (`ofNat C.k` at `while.body.i`) is refuted by `hkge : C.k < %k.2.i` |
| `WalkLoopEnd` | **supplied: four fields, each a fact about the input, and three of them named here for the first time.**  `facts` is `HlastFacts`, whose producer is `hlastFacts_of_staging` (itself a bundle of supplied facts — the head's byte and class bits, the register cells and the calls' outcomes); `mergeWords` is `WalkMergeWords` at every state at `cleanup478.i`, and `refuseWords` is `WalkRefuseWords` at every state at `if.then`; `nepBound` is the merge's `%nep` value, which the dispatch's outcome names.  The *runs* are no longer supplied: `WalkLoopEnd.merge` and `WalkLoopEnd.refuse` produce `WalkTargetPost` from the words and the state's own cells, and their proofs are the four terminal runs of `JsonStage2WalkTargetPost` — so what a caller still owes is the words, and each word names its producer: `%4`'s value the seed's register carrier (`walkSeedFinalEnv_regs`, unless `"%4"` joins `walkStaticNames`), the log's arena word the write-back block `if.else285.i`'s link (`WalkInv.log_alen` is only the bound), the finalisation's seven registers the seed's environment (`walkEntryState_env`), the merge's root-done word a presence clause on `WalkInv`, and R0's refusal word a memory-carrying refusal segment — the last two are not clauses for the reasons their docstrings give (`walkWide` omits the four `alloca` slots, and a `WalkSegment` keeps no memory). |

Of the four, `WalkHeadCells` is the one that was *vocabulary* rather than an
input, and it is no longer a premise: the two clauses are `WalkInv` fields now, and
`mergeHeadCells`/`walkHeadCells` read them at the head state.  The rest are supplies a
caller makes from the record.  `WalkStringResidue` is the newest row and
the one the two-entry token's path is now a theorem from: its fields name their producers
where they are stated, and each one's retirement is named with it. -/

/-! ### Axiom footprints beyond the five -/

#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkCompletes_of_staging
/-- info: 'LeanLLVM.Refinement.WalkScope.stage2Post_of_staging_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.stage2Post_of_staging_loop
#print axioms LeanLLVM.Refinement.WalkScope.WalkLoopEnd.merge
#print axioms LeanLLVM.Refinement.WalkScope.WalkLoopEnd.refuse

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_of_continue
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStep_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushAt_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkPremises_of_staging

end WalkScope
end LeanLLVM.Refinement
