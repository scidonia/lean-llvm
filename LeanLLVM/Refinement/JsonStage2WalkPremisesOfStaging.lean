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
  terminal *posts* and the merge's count.  The result is the arm's own: where an entry is
  left, `HcontArm.dispatch` runs the class's producer — `walkDispatch_at_continue_cells_ws`
  for the whitespace bundle, `walkDispatch_at_continue_cells` for the scan-free one,
  `WalkDispatchResult.ofStringMerge` at the string arm's residue,
  `walkDispatch_at_continue_scalar` for the plain-value route, `bracketRefuse_at` for the
  closing bracket at depth zero, `containerOpenMerge_at` for the container openers, or a
  default-arm arm's own composition (`lettersCleanupMerge_at`, `fCleanupMerge_at`,
  `classCMerge_at`, `runScanMerge_at`); and from the last entry's arm where it is not
  (`WalkLoopEnd.dispatch`).  The posts are
  `WalkLoopEnd.merge`/`.refuse`'s, which produce `WalkTargetPost` from the word bundles and
  the state's own cells.
* **The loop's post** is `stage2Post_of_staging_loop`: the seed's prefix, the invariant
  and `walkLoopFinishesThree`'s triple, which names the returned verdict and memory, and
  the boundary at that memory is the post.

Two bundles are what the loop's step reads, and each is the arm rather than a field per
fact.  They are **produced**, not premises: `walkContinueFacts_of_payload`
(`JsonStage2WalkDispatchContinuing`) and `walkLoopEnd_of_payload` (below) build them from
the payload groups, and the table states what each bundle's arms need.

| premise | what it is | why it is not derived |
|---|---|---|
| `WalkContinueFacts` | the **class** of the continuing entry at every head state with an entry left (`HcontArm`: `ws` = `HcontFacts`, `cleanup` = `HcontCleanupFacts` through `hcontCleanupFacts_of_staging` (`JsonStage2WalkDispatchCleanupOfStaging`), `twoEntry` = `HstringFacts` beside its residue through `hstringFacts_of_staging` (`JsonStage2WalkDispatchStringOfStaging`), `scalar` = `HcontScalarFacts` through `hcontScalarFacts_of_staging` (`JsonStage2WalkDispatchScalarOfStaging`), `closeBracketZero` = the depth-zero refusal's own cells, `commaZero`/`colonZero` = their state-level producers `hcontArm_commaZero_of_staging`/`hcontArm_colonZero_of_staging` (`JsonStage2WalkDispatchZeroOfStaging`, which leave only the class and the depth split), `containerOpen` = the openers' nine-link merge, `closeWithOpen` = the closing delimiters' nesting check, `letters`/`fLetter`/`classC` = the default arm's spans on the scan-free class, and `run` = the same spans' run class) | each class's bundle is a fact about the token (`walkRevolutionMergeSegWs`'s own for `ws`, `walkRevolutionMergeSeg`'s for `cleanup`, `walkRevolutionMergeSegScalar`'s for `scalar`, `runScanMerge_at`'s for `run`), and the class is the head switch's arm and the tag test; the census over those (`HcontClass.complete`) is exhaustive by theorem, so the split is a value and the question is asked once.  For the produced classes the *bundle* is derived from named rows; what no producer derives is the document's content (the head byte's class bits, the entry lane and its order, the byte the whitespace check reads and its class, the log words and the decoded length) and the callee staging, which the census's §2 names per arm |
| `WalkLoopEnd` | the last entry's **arm** (one constructor per head-switch arm class, the default arm's spans split by the run/scan-free continuation) | the arm is supplied at the last-entry head states (`LastEntryArm`) — every constructor has a producer, `.highByte` through `hlastFacts_of_staging` applied by the dispatch to its `HlastResidue`, `.scalar` through `lastEntryArm_scalar_of_staging` (`JsonStage2WalkDispatchScalarOfStaging`) and `.run` through `runLastFacts_of_staging` (`JsonStage2WalkDispatchRunOfStaging`, whose bundle keeps only the segments, the tail's calls, the traversal and the document's price) — and the log's arena word is not a field: `merge` and `refuse` read it from the state's `WalkInv` (`walkMergeWords_of_inv`, `walkRefuseWords_of_inv`).  The rest of what the runs read is derived and deleted from the bundles: the seven finalisation registers and `%4` are `walkStaticRegs` entries (`walkFinalEnv_of_regs`, `walkMerge4_of_regs`), the merge's `%nep` value is `WalkLoopEnd.nepBound`, the root-done word is `WalkInv.root_slot` read as four bytes (`walkRootWord_of_hasBytes`), and the copy's `%off` word is the refusal segment's own store (`WalkRefuseSegment`), carried by the dispatch's `refuse` arm.  The *dispatch* is proved from the arm (`WalkLoopEnd.dispatch`), and the *runs* are proved, not supplied: `WalkLoopEnd.merge`/`.refuse` compose them from `JsonStage2WalkTargetPost`'s four routes |

The two-entry token's residue is now an **arm field** rather than a third premise:
`HcontArm.twoEntry` carries the state's `HstringResidue` beside its `HstringFacts` and the
arm's own accepting selector, so the loop's step and the obligation no longer take
`WalkStringResidue` externally.  The residue is **empty**: the log's arena-base word and
the log's base word are `WalkInv`'s `log_dst` and `log_base` at the head's memory, and
`stringPath_seg` reads them off the invariant.  The rest of what the fifteen links read is
*derived*: the answer and its call
(`s2StringBody_answers`), its word (`stage2StringBody_head_form`, on
`stage2StringBody_form_congr`), the decoded length and its word
(`s2StringBody_outn_le`, `s2StringBody_outn_at_call`), the
log's base word at the answer's memory (`strPath9`'s carry), the two staged addresses with
the cursor's signed bound (`stage2Pre`'s clauses, at `WalkGeom`), and the event count
(`WalkInv.events_le_of_tight` at the head, with the head's guard).  `stringPath_seg` is
the theorem from the invariant's clauses and the arm's selector.  The static carrier names `%c.i`,
`%z`, `%xp` and `%nxp` and `WalkIter` names `%arrayidx10.i`, so the residue carries no
register and no memory clause of the body.

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
import LeanLLVM.Refinement.JsonStage2WalkDispatchArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkRevolution
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg
import LeanLLVM.Refinement.JsonStage2WalkSeedAtEntry
import LeanLLVM.Refinement.JsonStage2WalkTargetPost
import LeanLLVM.Refinement.JsonStage2WalkArenaWord
import LeanLLVM.Refinement.JsonStage2WalkDispatchLastRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchContinuing

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

/-! **The continuing entry's facts, as the arm the head dispatch took.**  The evidence is
`HcontArm` (`JsonStage2WalkDispatchHcontArms`), one constructor per class of the emitted
head switch, and the census over those classes is `HcontClass.complete` — exhaustive over
the entry's first byte and the tag test *by theorem*, so no class's byte restriction is a
premise of another's:

* the **plain-value** class, `HcontArm.scalar`: the numeral route's four scalar pivots, the
  count test's succeeding arm, the no-run byte class and the tag test's true arm
  (`HcontScalarFacts`, `JsonStage2WalkHcontScalar`).  The document `"01"`'s byte `0x30`
  takes it, and `JsonStage2WalkHcontDomain` refutes the earlier split at exactly that
  head;
* the **high-byte** route's two one-entry classes, `HcontArm.ws` and `HcontArm.cleanup`:
  `HcontFacts`'s whitespace run and `HcontCleanupFacts`'s no-run continuation, both on the
  bytes 126 and 127;
* the **standalone string**, `HcontArm.twoEntry`: `HstringFacts` beside its
  `HstringResidue`, whose merge index is `C.k + 2`.  The bundle's `hsp0 : C.sp = 0` is
  the depth the arm is stated at, so this bullet covers the opener at depth zero; at
  positive depth the byte's head takes `land.lhs.true.i` and no constructor describes the
  merge or the refusal there (the census paragraph in
  `JsonStage2WalkDispatchHcontArms` names the missing route);
* the **container openers**, `HcontArm.containerOpen`: `[` and `{` through `if.then.i`,
  nine links to the merge (`containerOpenMerge_at`), priced at `9 + 2`;
* the **closing delimiter with a container open**, `HcontArm.closeWithOpen`: `]` and `}`
  through `if.then53.i`, the nesting check's four sub-routes (`closeWithOpen_at`);
* the **default arm's letter and high-byte route on the scan-free class**,
  `HcontArm.letters`: `lettersSpan`'s four links below `if.else387.i`, with the head's chain
  to the seam and the tail's three calls as their own counted segments — twenty links,
  `lettersCleanupMerge_at`, dispatched at the staged documents `"a0"` and `\xC8 0`
  (`JsonStage2WalkDispatchLettersDomain`);
* the **default arm's `'f'` leaf on the scan-free class**, `HcontArm.fLetter`: `fSpan`'s
  four links below `if.else387.i` through `LeafBlock54`'s *true* arm (`if.then397.i`,
  kind `9`), with the head's chain and the tail's three calls as their own counted segments
  — twenty links, `fCleanupMerge_at`, dispatched at the staged documents `"f0"` and `"f"`
  (`JsonStage2WalkDispatchFLetterDomain`);
* the **class-C span's leaves on the scan-free class**, `HcontArm.classC`: the bytes
  `110 … 125`, whose span is the byte's own `Seg` at `nS ≤ 5` (`c56TrueSpan`,
  `c56ElseSpan`, `c58TrueSpan`, `c58ElseSpan`) and whose tail and merge are
  `classCMerge_at`'s — at most `12 + 5 + 4 = 21` links, dispatched at `"n0"`, `"o0"`,
  `"t0"`, `"u0"`, `"n"` and `"u"` (`JsonStage2WalkDispatchClassCDomain`);
* the **default arm's run class at the continuing head**, `HcontArm.run`: the whitespace
  skip, the seam, the byte's span, the tail's *scan* arm, the landing, the visits by
  `scanRoundsAt` — the rounds at the seam's own bound `%cond350.i`, not `scanWsRounds`'s
  bundle projection — the exit and the merge, with the merge's three cells at the composed
  endpoint (`runScanMerge_at`), dispatched at `"a0"` (`JsonStage2WalkDispatchRunDomain`);
* the **last entry's run class**, `LastEntryArm.run`: the same path with `nH ≤ 11 + N` and
  the terminal price read at the credit boundary — `mergeLast`'s byte term is the document
  bytes the entry has left to reach, so the run and the scan's `4·(c - 1 - i)` are paid out
  of the potential rather than out of a six-link allowance (`RunLastFacts`,
  `runLastMerge_at`, applying `runLast_price_with_credit` to the bundle's three document
  bounds), dispatched at `"a "` (`JsonStage2WalkDispatchRunLastDomain`).  Every
  other class at the last entry is proved as well — `.letters`, `.fLetter`, `.classC`, the
  refusal arms and `.highByte` — so the last entry's arm has no `supplied` constructor at
  its level.  The continuing level has no hole there either: the opener's depth-zero arm is
  `HcontArm.twoEntry`, and the same byte at positive depth is
  `HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`, whose producer is
  `hcontArm_stringOpenAboveZero_of_class` (`JsonStage2WalkDispatchClassCase`) from the
  payload's `abi.openCall` and the class rows' `deep` split, over the two staging
  producers in `JsonStage2WalkDispatchHcontStringDeep`.  What the census still reads is
  the payload tier — the document's content and the callee's staging — not a class
  without an arm.

**The high-byte route is proved, not supplied.**  `126` and `127` are the class
`HcontArm.ws`/`.cleanup` carry (`HcontFacts`, `HcontCleanupFacts`), with the counted
segments `walkRevolutionMergeSegWs` and `walkRevolutionMergeSeg`; an earlier revision of
this row named that route as owed, and that was stale.

The case is a value and not a second conjoined premise.  Two premises would be jointly
uninhabited at exactly the input the walk handles: at `C.k = 0`, `G.nep = 2` the head's
test `0 + 1 < 2` is true, so the continuing branch runs, and each class's evidence is a
different bundle.  The class question therefore has to be answered where the producer
knows the answer (the head's byte and its tests), and this is where it is answered.

**What the class case has, and what it still reads.**  The per-class rows are
`HcontClassRows`' (`JsonStage2WalkDispatchClassRows`) and each of the classes whose rows
they are has its branch (`JsonStage2WalkDispatchClassCase`: `hcontArm_scalar_of_class`,
`hcontArm_letters_of_class`, `hcontArm_fLetter_of_class`, the four
`hcontArm_classC_*_of_class`, `hcontArm_cleanup_of_class` and
`hcontArm_stringOpenAboveZero_of_class`).  `.run` is armed as well: the class rows'
`run` field produces a `Nonempty HcontArm` from a `HcontRunRow` (`hcontRunRow_of_rows`
joined to `RunFacts` at the class's prefix, with `runSkip`'s stop and `runTail`'s rows),
and `walkContinueArm_of_payload` (`JsonStage2WalkDispatchContinuing`) carries the `.run`
branches (`hcontArm_run_otherValue`, and
`hcontArm_run_defaultValueLow`/`_Mid`/`_Bracket`/`_BracketHigh`/`_Brace`) at the
whitespace classes.  What remains supplied is the producer tier those arms read — the
class rows' `runSkip`/`runTail` for `.run`, and `HcontWsRows` for the whitespace arm `.ws`
beside it — not a branch.  The two arms' constructors are stated
at the state's own root word (`HcontArm.stringOpenAboveZeroMerge`/`.Refuse`,
`hcontArm_cleanup_of_rows`), so the class is not narrowed to the states where that slot
holds `0`.

The abbreviation is `JsonStage2WalkDispatchHcontArms`'s, beside the `HcontArm` inductive —
the bundle is the arm, and the arm's own module names it.  Its producer is
`walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing`), which reads the
payload's rows: no `∀ G` producer is a theorem, because each arm's evidence carries
supplies at a reachable state; the class case is what turns those rows into the arm. -/

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

/-- **The last entry's arm and the terminal blocks' log word**, at every state each is
read at.  `hlast` is the last entry's **arm** — one constructor per control-flow arm of the
pinned head switch, with the default arm's spans split into the scan-free and run
continuations (`LastEntryArm`, `JsonStage2WalkDispatchArms`) — and
`WalkLoopEnd.dispatch` applies the arm's own producer to it, so what is supplied is
per-arm evidence and not a bundle whose class is another arm's; `mergeWords` and
`refuseWords` are that block's log word, which no clause carries.

The terminal post is not a field: `WalkLoopEnd.merge` and `WalkLoopEnd.refuse` produce it
from the bundle, the state's own cells and the word the dispatch's refusal arm carries,
and their proofs are the four terminal runs of `JsonStage2WalkTargetPost`.  So what this
structure *supplies* is the arm and the log's word, and what the layer *proves* is the
dispatch's result, the run and the boundary at its memory.

**What is supplied, and what is derived.**

* derived: the finalisation's seven registers (`WalkFinalEnv`), because all seven names
  are entries of `walkStaticRegs` and `WalkInv.regs` answers them
  (`walkFinalEnv_of_regs`);
* derived: `%4`'s cell, which is `walkStaticRegs`'s `%4` entry (`walkMerge4_of_regs`);
* derived: the merge's `%nep` value, `WalkLoopEnd.nepBound` below — the same carrier
  names `%nep` as `BitVec.ofNat 64 G.nep`, and the document's width makes the word its
  own number;
* derived: the merge's root-done word.  `WalkInv.root_slot` is presence over
  `G.next0 + 8`'s four bytes and the test reads an `i32`, so
  `walkRootWord_of_hasBytes` names the word (`JsonStage2WalkTargetPost`);
* derived: the refusal copy's `%off` word.  The refusing block's store is the last write
  before `if.then`, and `WalkRefuseSegment` (`JsonStage2WalkTraverse`) carries it from
  the branch that made it, so it arrives with the dispatch's `refuse` arm.

The log's arena word is derived too: the finalisation's copy loads `%z + 48`, whose word
is `WalkInv.log_alen`'s witness, and the record reports it as the decoded extent.  So the
structure supplies the arm and nothing else.

**Consequence for the top level.**  `∀ G, WalkLoopEnd G` is still *not* a theorem,
because `hlast` is real per-input arm evidence and not a `WalkInv` consequence.  That is
the honest shape: the bundle's remaining supply is the last entry's dispatch, which is
what a producer must build.  `stage2WalkObligation_of_staging`
(`JsonStage2WalkFlushPost`) remains a true conditional, and the claim to quote as closure
is `stage2WalkObligation_of_premises` (`JsonStage2WalkAssembly`), whose statement names
the per-input `WalkPremises` and the record's post rule and no bundle.  The other bundle,
`WalkContinueFacts`, is class data: no `∀ G` producer exists either, because each arm's
evidence carries a tail `WalkSegment` and the scan's traversal hypotheses that are
supplies at a reachable state rather than `WalkInv` consequences
(`JsonStage2WalkHcontFactsOfStaging`'s map).

**The states the census once had no arm for are armed.**  `}` (`125`) at depth
zero takes `LeafBlock15 → if.then53.i → if.then56.i` and its refusal store — the bracket's
two blocks at the brace's pivots — and a container opener at depth `520` takes
`if.then.i`'s call and `if.end.i`'s `ugt` arm to `if.then21.i`; and an opener whose
value-position answer is `0` takes `if.then.i`'s other branch, `if.then16.i`'s offset
store.  All three now have their own
constructors at both levels (`.closeBraceZero`, `.openAtCap`, `.containerOpenRefuse`),
their own producers
(`hcontArm_closeBraceZero_of_staging`, `lastEntryArm_closeBraceZero_of_staging`,
`hcontArm_openAtCap91_of_staging` … `lastEntryArm_openAtCap123_of_staging`,
`hcontArm_containerOpenRefuse91_of_staging` … `lastEntryArm_containerOpenRefuse123_of_staging`)
and their own counted, priced segments (`closeBraceZero_at`, `containerOpenCap_at`,
`containerOpenRefuse_at`), so a producer of
`hlast` or of `HcontArm` can be written at those states like at any other: the enum is no
longer the obstruction there.  What the bundle still takes, per class, is
`JsonStage2WalkDispatchResidual`'s table — the arm's payload — and the two arms' `520` is
the invariant's own cap (`depth_cap`), so the depth is a state's rather than a document's;
the answer split is the callee's own two values (`s2ValuePos_ret_zero_or_one`), so it is a
state's too.
`JsonStage2WalkDispatchResidual` records what the holes were and what fills them. -/
structure WalkLoopEnd {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- **The last entry's arm**, at every head state the merge's test sends to the exit.
  It is the dispatch's evidence, not its conclusion: `WalkLoopEnd.dispatch` applies
  `LastEntryArm.dispatch` to it, so each arm's own premises are what the caller supplies
  and no arm's class is a premise of another's. -/
  hlast : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) → LastEntryArm (stage2Calls stage2SubCalls) G C s

/-- **The merge's `%nep` value is inside the stream**: the last entry's price is stated
against the credit its index consumed, and this is what makes that credit the
potential's.  `%nep` is `walkStaticRegs`'s `BitVec.ofNat 64 G.nep`, so the merge's `phi`
reads the parameter; `G.nep < 2 ^ 64` (`nep_le` at the document's width) makes the word
its own number, so the bound is the entry count's. -/
theorem WalkLoopEnd.nepBound {m0 : Mem} {G : WalkGeom m0}
    (Cd : WalkCarry G) (sd : State) (nepv : BitVec 64)
    (_hInv : WalkInv G Cd sd) (_hblk : Cd.block = "cleanup478.i")
    (hnep : lookupName sd.env "%nep" = some (.int 64 nepv)) : nepv.toNat ≤ G.nep := by
  have hcell : lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) :=
    _hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  have hword : (some (.int 64 nepv) : Option Value) = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [← hnep]; exact hcell
  have h64 : G.nep < 2 ^ 64 := by
    have hle := G.nep_le
    have hdoc := G.maxDoc
    simp only [stage2MaxDocument] at hdoc
    omega
  cases hword
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]

/-- **The last entry's dispatch, from its arm.**  `LastEntryArm.dispatch`
`(JsonStage2WalkDispatchArms`) at the state the field is read at: each arm runs its own
producer — the scalar arm's path, the preserved high-byte path, the two refusals, the
openers' nine links, a default-arm span's own composition, or the last entry's run class —
and the loop's guard is read by
`WalkInv.head_lt` only where an arm needs the last index.  So the field's reader and the
dispatch's producer cannot drift apart, and no arm carries another's byte class. -/
theorem WalkLoopEnd.dispatch {m0 : Mem} {G : WalkGeom m0} (h : WalkLoopEnd G) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      ¬ (C.k + 1 < G.nep) →
      WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  fun C s hInv hhead hnot => (h.hlast C s hInv hhead hnot).dispatch hInv hhead hnot

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
  exact walkFinishPost_merge G Cd sd hInv
    hblk hpre hsp hspv hk hkv hnep hterm (walkMergeWords_of_inv hInv)

/-- **The refusal copy's terminal post, from the copy's word.**  R0: the state is at
`if.then` already, so the post is the copy's two steps at the word the previous link
stored — carried to the copy as the refusal segment's own field. -/
theorem WalkLoopEnd.refuse {m0 : Mem} {G : WalkGeom m0} (h : WalkLoopEnd G)
    (Cd : WalkCarry G) (sd : State) (hInv : WalkInv G Cd sd)
    (hblk : Cd.block = "if.then")
    (hword : ∃ k, k ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k)) :
    WalkTargetPost (stage2Calls stage2SubCalls) G Cd sd :=
  walkFinishPost_refuseOfWords G Cd sd hInv hblk hword

/-- **The loop's step, from the continuing arm and the last entry's arm.**
`walkLoopStepThree_of_dispatchResult` (`JsonStage2WalkDispatchThreeOfRun`) asks for the
dispatch's result at every head state, the finalisation's two terminal runs and the merge's
count.  The result is the dispatch's own: where an entry is left, the continuing premise's
`HcontArm` names the class and `HcontArm.dispatch` runs that class's producer — the
whitespace run, the scan-free continuation, the standalone string at its residue, the
plain-value numeral route, the container openers, a default-arm span's own composition, or
the default arm's run class at its own segment;
where it is not, the last entry's arm runs (`WalkLoopEnd.dispatch`).  The runs and the
count are `WalkLoopEnd`'s.

**What the branch on `C.k + 1 < G.nep` now is, and what it is not.**  It selects *which
premise describes the head state* — the continuing entry's arm or the last entry's arm —
because the two are the input's facts about those two states.  It no longer decides the
dispatch's outcome, and it no longer names a byte class: both arms are classified by the
head switch's own arms (`HeadArm` beside `HcontClass`), and the plain-value arm is the one
an ordinary numeral takes, where the old residue demanded the bytes 126 and 127.  Both
branches build the same dispatch's result — `merge` below the stream's end and `mergeLast`
at it, which differ only in the price they state — and `WalkDispatchResult.toOutcome`
classifies it by the merge's index against `%nep`.  So the `finish` outcome is reachable
from either branch, and the standalone string's `finish` is what
`standaloneString_finish` states.

**The continuing branch is the continuing census's arm, and the residue is an arm field.**
`HcontArm` (`JsonStage2WalkDispatchHcontArms`) has one constructor per class of the emitted
head switch: the plain-value numeral route (`scalar`), the high-byte route's whitespace and
scan-free one-entry classes, the standalone string (`twoEntry`, carrying its own
`HstringResidue`), the container openers (`containerOpen`), and the default arm's spans on
the scan-free and run classes (`letters`, `fLetter`, `classC`, `run`) — every one proved,
with no `supplied` constructor left.  The standalone string's two depths are two arms:
`twoEntry`'s bundle pins `C.sp = 0` for the depth-zero half, and `land.lhs.true.i`'s
route at positive depth is `HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`,
produced by `hcontArm_stringOpenAboveZero_of_class` (`JsonStage2WalkDispatchClassCase`)
from the payload's `abi.openCall` and the class rows' `deep` split.  So no class is
unarmed — the positive-depth opener this paragraph once named as the one class without an
arm has its pair of constructors and their producers (`JsonStage2WalkDispatchResidual`
records the history) — and what the census still reads is the payload's rows, not a hole.  The class question is
answered where the producer knows it — the head's byte and its tag test — and
`HcontClass.complete` proves the *byte* census exhaustive.  So the loop's step takes
no `WalkStringResidue` beside the continuing premise: the residue is the string arm's
field, and the branch is a value rather than a re-shaping of every consumer. -/
theorem walkLoopStep_of_staging {m0 : Mem} {G : WalkGeom m0}
    (hcont : WalkContinueFacts G) (hend : WalkLoopEnd G) :
    WalkLoopStepThree (stage2Calls stage2SubCalls) G 27 :=
  walkLoopStepThree_of_dispatchResult (Nat.le_refl 27)
    (fun C s hInv hhead => by
      by_cases hk : C.k + 1 < G.nep
      · exact (hcont C s hInv hhead hk).dispatch hInv hhead hk
      · exact hend.dispatch C s hInv hhead hk)
    (fun Cd sd p spv k2 prev spOp kOp nepv hInv hblk hpre hsp hspv hkOp hk2 hnepv hterm =>
      hend.merge Cd sd p spv k2 prev spOp kOp nepv hInv hblk hpre hsp hspv hkOp hk2 hnepv
        hterm)
    (fun Cd sd hInv hblk hword => hend.refuse Cd sd hInv hblk hword)
    (fun nepv Cd sd hInv hblk hnep => WalkLoopEnd.nepBound Cd sd nepv hInv hblk hnep)

/-! ### The last entry's arm, by class

`HcontClass.complete` is the head switch's census at the last entry's byte, and the class
case reads one premise per class: the derived bytes take the invariant's cells and the
class bit, the openers take the payload's `openCall` group plus the depth and the answer,
the high-byte class takes `HlastLane`/`HlastAbi.highByte`, and the default arm's four
classes take the `HlastArmRows` groups — `.scalar` on the tag test's true arm, and at the
false one `.run` when the byte before the entry's end is whitespace, else `letters`/
`'f'`/class C by the head byte's own two pivots.

No branch assumes a segment: the chains, spans and tails are the groups' fields, and the
segments the derived classes need are the producers' own compositions. -/
noncomputable def walkLoopEnd_of_payload {m0 : Mem} {G : WalkGeom m0}
    (hp : HlastPayload G) (hc : HlastClassRows G) (ha : HlastArmRows G) :
    WalkLoopEnd G := by
  refine ⟨fun C s hInv hblock hnot => ?_⟩
  -- the default arm, on the tag test's false side: whitespace is the run class, else a leaf
  have defaultArm : (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) →
      evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1 →
      LastEntryArm (stage2Calls stage2SubCalls) G C s := by
    intro hbit h125
    by_cases hws : wsStop G (G.n - 1)
    · obtain ⟨N, Cm, sm, nH, hHead, hnH, hm, hmk, Cs, ss, nS, hSpan, hnS, hs, Ct, st,
        hTail, ht, htk, Cl, tl, hLatch, hl, hkC, i, c, hcounter, hbound, hic, hbyte,
        hstop, hN, hcl⟩ := ha.run C s hInv hblock hnot hbit hws
      exact lastEntryArm_run_of_staging C s hInv hbit N hHead hnH hm hmk hSpan hnS hs
        hTail ht htk hLatch hl hkC i c hcounter hbound hic hbyte hstop hN hcl
    · by_cases h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1
      · by_cases h102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 1
        · obtain ⟨Cm, sm, nH, hHead, hnH, hm, hmk, h8m, Ct, st, tok, hTail, ht, htk,
            htok⟩ := ha.fLetter C s hInv hblock hnot hbit h110 h102
          exact lastEntryArm_fLetter_of_staging C s hInv rfl hbit h110 h102 hHead hnH hm
            hmk h8m hTail ht htk htok
        · obtain ⟨Cm, sm, nH, hHead, hnH, hm, hmk, h8m, Ct, st, tok, hTail, ht, htk,
            htok⟩ := ha.letters C s hInv hblock hnot hbit h110 (bitZeroOfNeOne h102)
          exact lastEntryArm_letters_of_staging C s hInv rfl hbit h110 (bitZeroOfNeOne h102)
            hHead hnH hm hmk h8m hTail ht htk htok
      · obtain ⟨Cm, sm, nH, hHead, hnH, hm, hmk, h8m, Cs, ss, nS, hSpan, hs, hnS, Ct, st,
          tok, hTail, ht, htk, htok⟩ :=
          ha.classC C s hInv hblock hnot (bitZeroOfNeOne h110) h125
        exact lastEntryArm_classC_of_staging C s hInv rfl (bitZeroOfNeOne h110) h125 hHead
          hnH hm hmk h8m hSpan hs hnS hTail ht htk htok
  by_cases h34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1
  · exact lastEntryArm_stringOpener_of_staging C s hInv h34 hnot
  · by_cases h44 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 44) = 1
    · -- `%8 < 44`: the low class
      exact defaultArm (hlast_tag_low (hlastByte G C) h44)
        (Or.inl (slt_one_of_toInt_le (by decide) h44))
    · by_cases h44eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1
      · -- the comma
        by_cases hsp : C.sp = 0
        · exact lastEntryArm_commaZero_of_staging C s hInv h44eq hsp
        · exact lastEntryArm_commaAboveZero_of_staging C s hInv h44eq hsp
      · by_cases h58 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 58) = 1
        · -- `44 ≤ %8 < 58`: the tag test chooses the numeral route or the letters one
          by_cases hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
              evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
          · obtain ⟨hb13, hb32, hbne32, r₁, r₂, r₃, rdv, xA, hreadT, hpre₁, hcall₁,
              hret₁, hbit0T, hpre₂, hcall₂, hret₂, hpre₃, hcall₃⟩ :=
              ha.scalar C s hInv hblock hnot (bitZeroOfNeOne h44) h58
                (bitZeroOfNeOne h44eq) hbit
            exact lastEntryArm_scalar_of_staging G C s hInv hblock hnot rfl
              (bitZeroOfNeOne h44) h58 (bitZeroOfNeOne h44eq) hb13 hb32 hbne32 hbit
              r₁ r₂ r₃ hreadT hpre₁ hcall₁ hret₁ hbit0T hpre₂ hcall₂ hret₂ hpre₃ hcall₃
          · exact defaultArm (bitZeroOfNeOne hbit)
              (Or.inl (slt_one_of_toInt_le (by decide) h58))
        · by_cases h58eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1
          · -- the colon
            by_cases hsp : C.sp = 0
            · exact lastEntryArm_colonZero_of_staging C s hInv h58eq hsp
            · exact lastEntryArm_colonAboveZero_of_staging C s hInv h58eq hsp
          · by_cases h91 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 91) = 1
            · -- `58 ≤ %8 < 91`
              exact defaultArm (hlast_tag_mid (hlastByte G C) h91 (bitZeroOfNeOne h58))
                (Or.inl (slt_one_of_toInt_le (by decide) h91))
            · by_cases h123 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 123) = 1
              · by_cases h93 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 93) = 1
                · by_cases h91eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1
                  · -- the open bracket
                    obtain ⟨rdv, hread, hpreV, r, hcall⟩ :=
                      hp.abi.openCall C s hInv hblock hnot
                    by_cases h1 : r.ret = .int 32 (BitVec.ofNat 32 1)
                    · by_cases hsp : C.sp ≤ 519
                      · exact lastEntryArm_containerOpen91_of_staging C s hInv h91eq hsp
                          hread hpreV r hcall h1
                      · have h520 : C.sp = 520 := by
                          have hcap := hInv.depth_cap
                          simp only [stage2StackExtent] at hcap
                          omega
                        exact lastEntryArm_openAtCap91_of_staging C s hInv h91eq h520
                          hread hpreV r hcall h1
                    · have h0 : r.ret = .int 32 (BitVec.ofNat 32 0) := by
                        rcases s2ValuePos_ret_zero_or_one hcall with h | h
                        · exact absurd h h1
                        · exact h
                      exact lastEntryArm_containerOpenRefuse91_of_staging C s hInv h91eq
                        hread hpreV r hcall h0
                  · -- `91 < %8 < 93`: the bracket class's own bytes
                    exact defaultArm
                      (hlast_tag_bracket (hlastByte G C) (bitZeroOfNeOne h91) h123 h93)
                      (Or.inl (slt_one_of_toInt_le (by decide) h123))
                · by_cases h93eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1
                  · -- the close bracket
                    by_cases hsp : C.sp = 0
                    · exact lastEntryArm_closeBracketZero_of_staging C s hInv h93eq hsp
                    · exact lastEntryArm_closeWithOpen93_of_staging C s hInv h93eq hsp
                        (s2AfterValuePre_of_inv hInv hsp)
                  · -- `93 ≤ %8 < 123`
                    exact defaultArm
                      (hlast_tag_bracketHigh (hlastByte G C) (bitZeroOfNeOne h91) h123
                        (bitZeroOfNeOne h93))
                      (Or.inl (slt_one_of_toInt_le (by decide) h123))
              · by_cases h125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 1
                · by_cases h123eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1
                  · -- the open brace
                    obtain ⟨rdv, hread, hpreV, r, hcall⟩ :=
                      hp.abi.openCall C s hInv hblock hnot
                    by_cases h1 : r.ret = .int 32 (BitVec.ofNat 32 1)
                    · by_cases hsp : C.sp ≤ 519
                      · exact lastEntryArm_containerOpen123_of_staging C s hInv h123eq hsp
                          hread hpreV r hcall h1
                      · have h520 : C.sp = 520 := by
                          have hcap := hInv.depth_cap
                          simp only [stage2StackExtent] at hcap
                          omega
                        exact lastEntryArm_openAtCap123_of_staging C s hInv h123eq h520
                          hread hpreV r hcall h1
                    · have h0 : r.ret = .int 32 (BitVec.ofNat 32 0) := by
                        rcases s2ValuePos_ret_zero_or_one hcall with h | h
                        · exact absurd h h1
                        · exact h
                      exact lastEntryArm_containerOpenRefuse123_of_staging C s hInv h123eq
                        hread hpreV r hcall h0
                  · -- `123 ≤ %8 < 125`
                    exact defaultArm
                      (hlast_tag_brace (hlastByte G C) (bitZeroOfNeOne h91)
                        (bitZeroOfNeOne h123) h125)
                      (Or.inl h125)
                · by_cases h125eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1
                  · -- the close brace
                    by_cases hsp : C.sp = 0
                    · exact lastEntryArm_closeBraceZero_of_staging C s hInv h125eq hsp
                    · exact lastEntryArm_closeWithOpen125_of_staging C s hInv h125eq hsp
                        (s2AfterValuePre_of_inv hInv hsp)
                  · -- `%8` is 126 or 127: the high-byte class
                    exact lastEntryArm_highByte_of_payload (G := G) (C := C) (s := s) hInv
                      hblock hnot (bitZeroOfNeOne h125) (bitZeroOfNeOne h125eq) hp

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
`walkLoopStep_of_staging` at the two bundles.

The stage is `walkStage_at_pre_fields`', so the flush and the seed are stated at the
record's numbers: those lemmas read `WalkStage`'s fields, `WalkPremises` names the
record's, and the fields' equalities are the construction's.

The two bundles the loop's step reads are **produced here**, one per level: the continuing
entry's class is `walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing`) at the
payload, the class rows and the whitespace rows, and the last entry's arm with the
finalisation's two log words is `walkLoopEnd_of_payload` at the last payload and its two
row groups.  So this theorem's premises are the payload groups, not the bundles.  The
two-entry token's residue is not a third: it is `HcontArm.twoEntry`'s field.  The merge's
two register cells are not premises either: they are `WalkInv` clauses, and
`mergeHeadCells` reads them at the head state.

**Why the bundles are still not `∀ G` theorems.**  Their producers' arguments are rows
about the document and the call environment, and those rows are per-input supplies: the
census has an arm at every state the invariant admits — `.closeBraceZero` and `.openAtCap`
were the two depth cases it once lacked, and the string opener at positive depth, the class
that had no arm, is `HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`
(`JsonStage2WalkDispatchHcontStringDeep`), with `.twoEntry`'s own `hsp0 : C.sp = 0`
covering the depth-zero half — so no state is excluded, but the rows the arms consume (the
tail's calls, the run's stop, the visits' class, the last byte's route) are the document's
and the staging's, not consequences of `WalkInv`.  `WalkLoopEnd`'s log words, by contrast,
*are* produced from the invariant: `mergeWords` and `refuseWords` read `WalkInv.log_alen`'s
witness `a ≤ C.alen`, which `walkMergeWords_of_inv` and `walkRefuseWords_of_inv` produce,
so what the last level still reads is the arm.  The closure claim to quote is
`stage2WalkObligation_of_premises` (`JsonStage2WalkAssembly`), which takes `WalkPremises`
and the post rule and no bundle; this theorem is the producer of its first premise. -/
theorem walkPremises_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), HcontPayload G)
    (hrows : ∀ {m0 : Mem} (G : WalkGeom m0), HcontClassRows G)
    (hws : ∀ {m0 : Mem} (G : WalkGeom m0), HcontWsRows G)
    (hlast : ∀ {m0 : Mem} (G : WalkGeom m0), HlastPayload G)
    (hlastRows : ∀ {m0 : Mem} (G : WalkGeom m0), HlastClassRows G)
    (hlastArms : ∀ {m0 : Mem} (G : WalkGeom m0), HlastArmRows G) :
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
        hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
      · rw [hargs, walkEntryState_env, hStok]
        simp [lookupName]
      · rw [hargs, walkEntryState_env, hSe]
        simp [lookupName]
      · rw [hargs, walkEntryState_env, hSs]
        simp [lookupName]
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
      · exact hnext.symm
      · rw [hargs, walkEntryState_env]
        simp [lookupName]
    · -- the loop's step, from the two bundles the payload groups produce
      exact walkLoopStep_of_staging (G := G)
        (walkContinueFacts_of_payload (hcont G) (hrows G) (hws G))
        (walkLoopEnd_of_payload (hlast G) (hlastRows G) (hlastArms G))

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

/-- **A fixed post carries from one outcome to every behaviour**, as
`stage2Post_of_completion` does for the existential one. -/
theorem Stage2PostFixed_of_completion {calls : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {sE : State} {B : Nat} {oGood : Outcome}
    {c ctype cst tok s z e d : Nat}
    (hcom : runFuel calls B stage2Body sE = some oGood)
    (hgood : Stage2PostFixed c ctype cst tok s z e d args mem next oGood) :
    ∀ o, BehFromState calls stage2Body sE o →
      Stage2PostFixed c ctype cst tok s z e d args mem next o := by
  intro o hbeh
  rcases hbeh with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hEq : oGood = Outcome.ub := (runFuel_outcome_unique hn hcom).symm
    rw [hEq] at hgood
    exact hgood.elim
  · have hEq := runFuel_outcome_unique hn hcom
    rw [hEq]
    exact hgood

/-- **The loop's post, at the staging.**  At `nep > 0` the entry block's test sends the
run into the loop; the seed's three steps (`walkSeedPrefix_entry_geometry`), the invariant
at the loop head (`walkSeedInvariant_geometry`), the loop's step and its completion
(`walkLoopFinishesThree` at `F ≤ 27`) give the returned verdict and memory, and the
boundary at that memory is the post. -/
theorem stage2PostFixed_of_staging_loop {d c ctype cst tok s z e : Nat}
    {a13 : List Value} {mem : Mem} {next : Nat} {G : WalkGeom mem} {S : WalkStage G}
    (hSc : S.c = c) (hSct : S.ctype = ctype) (hScs : S.cst = cst) (hStok : S.tok = tok)
    (hSs : S.s = s) (hSz : S.z = z) (hSe : S.e = e) (hSd : S.d = d)
    (hargs : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (hpos : 0 < G.nep) {F : Nat}
    (hloop : WalkLoopStepThree (stage2Calls stage2SubCalls) G F) :
    ∀ o, BehFromState (stage2Calls stage2SubCalls) stage2Body
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) o →
      Stage2PostFixed c ctype cst tok s z e d a13 mem next o := by
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
        mem next) hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    · rw [hargs, walkEntryState_env, hStok]
      simp [lookupName]
    · rw [hargs, walkEntryState_env, hSe]
      simp [lookupName]
    · rw [hargs, walkEntryState_env, hSs]
      simp [lookupName]
    · rw [hargs, walkEntryState_env]
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
  have hgood : Stage2PostFixed c ctype cst tok s z e d a13 mem next
      (.ret (some (.int 64 v)) m) := by
    -- the boundary is at the staging `S`; the record's numbers are `hSc`…`hSd`
    have hbS : Stage2BoundaryAtN S.c S.ctype S.cst S.tok S.s S.z S.e S.d
        (walkTargetArgs G) mem next m (.int 64 v) := by
      rw [← hnext]
      exact hb
    rw [hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd] at hbS
    have hbN : Stage2BoundaryAtN c ctype cst tok s z e d a13 mem next m (.int 64 v) := by
      simpa [walkTargetArgs, hargs] using hbS
    exact hbN
  intro o hb'
  exact Stage2PostFixed_of_completion hcom hgood o hb'

/-- **The loop's post, at the record's existential boundary**, projected from the
fixed form.  This is the statement `Γ_stage2at`'s post is, and it is derived so
the two forms cannot drift. -/
theorem stage2Post_of_staging_loop {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    {a13 : List Value} {mem : Mem} {next : Nat} {G : WalkGeom mem} {S : WalkStage G}
    (hSc : S.c = c) (hSct : S.ctype = ctype) (hScs : S.cst = cst) (hStok : S.tok = tok)
    (hSs : S.s = s) (hSz : S.z = z) (hSe : S.e = e) (hSd : S.d = d)
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
  intro o hb
  have hlen : a13.length = 13 := by rw [hargs]; rfl
  show stage2Post ((stage2Args a13 d c ctype cst tok s z e).take 13) mem next o
  rw [stage2Args_take13 a13 hlen]
  cases o with
  | ub =>
      exact stage2PostFixed_of_staging_loop hSc hSct hScs hStok hSs hSz hSe hSd hargs
        hnext hpos hloop .ub hb
  | ret v m =>
      cases v with
      | none =>
          exact stage2PostFixed_of_staging_loop hSc hSct hScs hStok hSs hSz hSe hSd hargs
            hnext hpos hloop (.ret none m) hb
      | some v =>
          obtain ⟨w, hw, -⟩ :=
            stage2PostFixed_of_staging_loop hSc hSct hScs hStok hSs hSz hSe hSd hargs
              hnext hpos hloop (.ret (some v) m) hb
          exact stage2Boundary_of_witness hw

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

/-- **The completion, at the payload groups.**  `stage2WalkCompletes_of_premises` at
`walkPremises_of_staging`: the body's run reaches an outcome inside the record's budget
whenever the record's pre and the adapter's staging hold.  Its premises are the six groups,
and the two bundles are produced from them, so no bundle enters as a hypothesis — the
`WalkLoopEnd` the last entry's arm yields has its log words from `WalkInv.log_alen`'s
witness, which is what makes the implication say something about a document rather than
about a refutable bundle. -/
theorem stage2WalkCompletes_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), HcontPayload G)
    (hrows : ∀ {m0 : Mem} (G : WalkGeom m0), HcontClassRows G)
    (hws : ∀ {m0 : Mem} (G : WalkGeom m0), HcontWsRows G)
    (hlast : ∀ {m0 : Mem} (G : WalkGeom m0), HlastPayload G)
    (hlastRows : ∀ {m0 : Mem} (G : WalkGeom m0), HlastClassRows G)
    (hlastArms : ∀ {m0 : Mem} (G : WalkGeom m0), HlastArmRows G) :
    Stage2WalkCompletes d c ctype cst tok s z e nkSlot nxpSlot stage2SubCalls :=
  stage2WalkCompletes_of_premises
    (walkPremises_of_staging hcont hrows hws hlast hlastRows hlastArms)

 /-! **The walk's obligation: the completion half here, the post half one module up.**
`Stage2WalkObligation` is `Satisfies` at `Γ_stage2at`, and its two conjuncts are the
completion (`stage2WalkCompletes_of_staging`, above) and the post at every behaviour of
the run.  The post's two arms are the empty entry stream's (`stage2Post_of_staging_flush`,
`JsonStage2WalkFlushPost`) and the loop's (`stage2Post_of_staging_loop`, above), and the
first of those lives above this module: `JsonStage2WalkFlushPost` imports this one, so
the record's obligation is stated there, where both arms are in scope. -/

/-! ### The premises, and what each one owes

The composition is complete; what remains is one premise per obstruction, and this is
the map.  None of them is a gap in the composition — each is either a fact about the
input or a named missing preservation lemma, and the two-entry residue is no longer a
top-level premise: it is `HcontArm.twoEntry`'s field.

| premise | status |
|---|---|
| `WalkContinueFacts` | **the continuing census's arms; each arm's evidence is a per-state supply, and no `∀ G` producer exists yet.**  The census is `HcontClass` (`JsonStage2WalkDispatchHcontArms`): the head switch's arms beside the tag test, exhaustive by `HcontClass.complete`.  The whitespace arm is `HcontFacts`' supply, in `HlastFacts`' discipline: its producer is `hlastFacts_of_staging`'s twin — the same three sources (the invariant's clauses, the document's content, the staging's addresses) read at the run class's states — and the bundle's fields are the head's byte and its four pivot bits, the entry counts and the default arm's cells, the whitespace class with its stop `k`, the seam's byte, the tail's segment and the scan's landing.  The run is derived rather than carried: `contWsRunF` composes it from the class field and `contWsPriceF` prices it.  That twin is `hcontFacts_of_staging` (`JsonStage2WalkHcontFactsOfStaging`), and what it takes from its caller is the document's bytes and their classes, the whitespace class, the tail's segment, the scan's landing and its traversal's three hypotheses (`hround`, `hguard`, `hbyte`, supplied unweakened), `htok`, which needs *the extra-token scan preserves a register it does not bind* — a statement a `WalkSegment` cannot carry, because the traversal returns its final state existentially.  The run's endpoint cells are not premises: `contWsRunF` returns the stop's `%cond350.i`, `wsSlS_envEnd` the seam's `%end.i`, and `%inc.i`/`%nep` are `WalkInv` clauses.  **The count test's value is `1` here and `0` in `HlastFacts`, and both are right**: the fields are arm-specific — a continuing entry has one after it, so the scan's bound is above its index, while the last entry's is the stream's end.  A docstring that gives either value without its arm reads as a contradiction in the other.  **`hnext` is derived, not supplied**: it follows from `C.k + 1 < G.nep` with the two counts pinned to `%k.0.i249 + 1` and `G.nep` (`cont_ult_one`), and `%inc.i`/`%nep` are clauses (`WalkInv.inc_reg`, `WalkInv.regs`) — so the group is closed.  The scan-free arm is `HcontCleanupFacts` (`JsonStage2WalkRevolution`), whose segment needs no scan, no tail budget and no traversal and whose price has no byte term.  **The plain-value arm is `HcontScalarFacts` (`JsonStage2WalkHcontScalar`)**, composed on the numeral route at sixteen links; it is the class the document `"01"` takes and the old split excluded, and `JsonStage2WalkHcontDomain` is the refutation at that head.  The two-entry arm is `HstringFacts` (`JsonStage2WalkDispatchWitnessString`) beside its `HstringResidue` — the residue is the arm's field now, so the loop's step and the obligation take no `WalkStringResidue` externally — and the fifteen-block segment there is **supplied rather than composed**: `WalkLink.z_arena_reserve_exit`'s address is now the staging's (it had stated `%xj.i` at `G.next0 + 16`, where the string body's `RegionsApart xj 8 outn 8` is false against `%outn.i = G.next0 + 20`; it is `+ 12` now), but the link still needs the register carriers `walkStaticRegs` omits and the two `s2StringBodyFoot`→`walkWide` frame lemmas, and the string body's call site has no `s2StringBodyPre` producer.  Its other groups come from the same three sources, and its two merge cells are fields at its own endpoint rather than `WalkInv` clauses. |
| `WalkContinueWsFacts` | **the whitespace class's `∀`-form; `walkDispatch_of_continue` reads it.**  Its content is `HcontFacts` at every head state with an entry left, and the dispatch bridge proves `WalkDispatch` from it with `walkDispatch_at_continue_cells_ws` (`JsonStage2WalkRevolutionSeg`), the whitespace arm's own composition.  `hcontFacts_of_staging` produces `HcontFacts` at *one* state, not this `∀` (a `∀` would have to inhabit `HcontFacts` at states whose class is another arm's, which is what the class split exists to avoid), which is why the loop's step calls the per-state dispatch instead.  The scan-free arm's `∀`-form is spelled in `walkDispatch_of_continue_cells` (`JsonStage2WalkRevolutionSeg`), which reads `HcontCleanupFacts` and is the same bridge for that arm.  The pair is kept so `WalkDispatch` keeps its only producer — `WalkDispatchOutcome.ofDispatch` and `WalkDispatch.revolution` consume that predicate — and the bridge is a two-line wrapper over the per-state dispatch, so the two cannot drift. |
| `WalkHeadCells` | **retired: proved, not supplied.**  `mergeHeadCells` (`JsonStage2WalkRevolutionSeg`) produces `MergeHeadCells` from `WalkInv` alone — `%inc.i` is `WalkInv.inc_reg` and `%nep` is one of `walkStaticRegs`' pairs — and `walkHeadCells` is its `∀`-form, which is what the loop's step and `walkDispatch_of_continue` read.  The clause is uniform (`ofNat 64 (C.k + 1)` at every block): the back edge (`walkBack_step`) advances neither `C.k` nor the register, and `whileBody_step` moves both together, so the block-keyed form this row used to propose (`ofNat C.k` at `while.body.i`) is refuted by `hkge : C.k < %k.2.i` |
| `WalkLoopEnd` | **the last entry's arm is supplied class data; the terminal blocks' log word is `WalkInv.log_alen`'s witness, derived rather than supplied.**  `hlast` is `LastEntryArm` — one constructor per control-flow arm of the head switch, the default arm's spans split into the scan-free and run continuations (`JsonStage2WalkDispatchArms`), each carrying its own arm's premises and nothing of another arm's class — and `WalkLoopEnd.dispatch` is the `def` that applies `LastEntryArm.dispatch` to it, so the reader cannot drift from the producers; there are no `mergeWords`/`refuseWords` fields: `merge` and `refuse` build `WalkMergeWords`/`WalkRefuseWords` from the state's `WalkInv` (`walkMergeWords_of_inv`, `walkRefuseWords_of_inv`).  The *runs* are not supplied: `WalkLoopEnd.merge` and `WalkLoopEnd.refuse` produce `WalkTargetPost` from the words and the state's own cells, and their proofs are the four terminal runs of `JsonStage2WalkTargetPost`.  So the supplied list is exactly `hlast`; the log's arena word is the invariant's, not a field.  The root-done word and the copy's `%off` word are no longer bundles: the first is `WalkInv.root_slot` read as four bytes (`walkRootWord_of_hasBytes`), the second is the refusal segment's own store (`WalkRefuseSegment`'s `word`), carried by the dispatch's `refuse` arm to `WalkLoopEnd.refuse`.  The rest is derived and no longer in the bundles: `%4`'s value and the finalisation's seven registers are `walkStaticRegs` entries, read by `walkMerge4_of_regs` and `walkFinalEnv_of_regs`, and the merge's `%nep` value is `WalkLoopEnd.nepBound`.  Each remaining supply names its producer: the scalar arm's premises are the byte's class and the tail's three calls (`scalarMerge_at`), the high-byte arm's is `HlastResidue`, the run arm's is `RunLastFacts` (composed by `runLastMerge_at` against `mergeLast`), and the log's arena word is `WalkInv.log_alen`'s witness: what is false at an escaping input is the *equality* with the carry's cursor — the write-back block `if.else285.i` stores the decoder's output length while `WalkInv.log_alen` relates the slot to the carry only by `≤` (`JsonStage2WalkArenaWord`) — so the post reports the word and the reserved extent separately and asserts no equality (`WalkMergeWords`' note). |

Of these, `WalkHeadCells` is the one that was *vocabulary* rather than an
input, and it is no longer a premise: the two clauses are `WalkInv` fields now, and
`mergeHeadCells`/`walkHeadCells` read them at the head state.  The two-entry token's
residue is no longer on the list either: it is `HcontArm.twoEntry`'s field, so the loop's
step and the obligation take only the continuing arm and the last entry's arm.
`WalkStringResidue`'s own fields name their producers where they are stated, and each
one's retirement is named with it.

### The two bundles: the verdict, and the claim to quote

The top-level theorem in the tree, `stage2WalkObligation_of_staging`
(`JsonStage2WalkFlushPost`), takes

```
(hcont     : ∀ {m0 : Mem} (G : WalkGeom m0), HcontPayload G)
(hrows     : ∀ {m0 : Mem} (G : WalkGeom m0), HcontClassRows G)
(hws       : ∀ {m0 : Mem} (G : WalkGeom m0), HcontWsRows G)
(hlast     : ∀ {m0 : Mem} (G : WalkGeom m0), HlastPayload G)
(hlastRows : ∀ {m0 : Mem} (G : WalkGeom m0), HlastClassRows G)
(hlastArms : ∀ {m0 : Mem} (G : WalkGeom m0), HlastArmRows G)
```

and the two bundles are produced from them — `walkContinueFacts_of_payload` and
`walkLoopEnd_of_payload` — so no bundle is a hypothesis.  Each bundle is still not a
`∀ G` theorem, and the two are not the same kind of obstruction:

| bundle | class | why it is not a `∀ G` theorem |
|---|---|---|
| `WalkContinueFacts` | **class data, a producer tier.**  The class is the head byte's switch arm, read from the document in `G` (`G.doc`, `G.entries`, `WalkInv.iter.reg8`) and exhaustive by `HcontClass.complete`; its per-class producers are `hcontFacts_of_staging`, `hcontCleanupFacts_of_staging`, `hstringFacts_of_staging`, `hcontScalarFacts_of_staging`, `hcontArm_*_of_staging`, … | Each arm's bundle carries a tail `WalkSegment` (the three callees' preconditions and answers at the call's own argument list).  The scan's traversal rows are no longer supplied: `hround`, `hbyte`'s read and `htok` are produced by `JsonStage2WalkRevolutionScanRound` (`scanRoundField`, `scanByteField`, `scanTokField`), so what remains of that group is the visited byte's class (`hbyteClass`), the document's content, and the old `hguard` is gone because `ScanGuard` is false at any state whose registers hold words.  Nothing is false; the document's facts are per input, which is why the bundle is a producer from rows — `walkContinueFacts_of_payload` — and not a `∀ G` theorem. |
| `WalkLoopEnd` | **class data: the last entry's arm.**  `hlast` is `LastEntryArm` (`LastEntryArm`, every arm with its own producer); the log's arena word is not a field — it is `WalkInv.log_alen`'s witness, which the finalisation's copy loads (`walkMergeWords_of_inv`, `walkRefuseWords_of_inv`) | The arm is built from the last level's payload and its two row groups — `walkLoopEnd_of_payload` — not from a `WalkInv` clause: each constructor is a class of the head switch and carries that class's producer's premises.  Nothing in the bundle is false, and the rows it reads are per input, exactly as the continuing bundle's are. |

Both rows are the same kind of obstruction — a per-class/per-arm producer tier — and that
tier is now built, from the payload groups rather than from the arms: the continuing bundle
by `walkContinueFacts_of_payload` and the last entry's by `walkLoopEnd_of_payload`.  The
three shape defects the continuing bundle's producer rows carried are
now repaired rather than described.  `HcontDefaultRow.hclass` is a `Type`-valued
classification (`HcontByteClass`: `.wsByte`, `.scanFree`, `.lowLeaf` or `.highLeaf`), each
arm taking its own disjunct and `HcontByteClass.complete` proving the four cover the byte,
so `HcontPayload` is inhabited at every head state with an entry left and
`HcontScanFree.not_wsStop` records the exclusion the old row had asserted; the visited-byte
row is stated at the visits' span (`k < p + 1`) in `hcontFacts_of_staging`, in
`scanByteField`, in every `hbyte` and in `ScanVisits`, which `cont_hbyteClass_not_wsCont`
(`JsonStage2WalkHcontFactsOfStaging`) certifies as the only consistent range; and the
whitespace seam's invariant and cells are the state group `HcontWsSeam` /
`hcontWsSeam_of_body` (`JsonStage2WalkDispatchSeams`), produced from `HcontRunBody` /
`contWsRunBody` (`JsonStage2WalkRevolution`) and the class-C span, so the tail follows
(`hcontScanTail_of_seam`) without the bundle's own `hTail`.
Neither bundle's *statement* is false, and the terminal post's numbers are the
invariant's own — the log's arena word is `log_alen`'s witness, reported as the decoded
extent, while the frame, presence and capacity clauses stay at the reserved extent.  The
top-level statement still carries its premises in the open, as `WalkPremises` does, rather
than behind a `∀ G`, so a reader can see exactly which tier remains.

So the honest closure claim is `stage2WalkObligation_of_premises`
(`JsonStage2WalkAssembly`), whose statement has neither bundle:

```
(h : WalkPremises d c ctype cst tok s z e nkSlot nxpSlot)
(hpost : ∀ args mem next, pre args mem next → ∀ o, BehFromState … → post args mem next o) :
  Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot
```

Its premises, classified:

* `h : WalkPremises` — **supplied per input, and the only remaining supply.**  Its empty
  stream arm is `walkFlushAt_of_staging` (a theorem from the staging); its loop arm's seed
  and invariant are `walkSeedPrefix_entry_geometry` and `walkSeedInvariant_geometry`
  (theorems); its loop step is `WalkLoopStepThree`, which is where the two bundles' work
  lands.  The stage is `walkStage_at_pre_fields`'s, so nothing in the shape is invented.
* `hpost` — **supplied: the record's post rule**, not read by the completion half.  The
  two staging arms produce it: `stage2Post_of_staging_flush`
  (`JsonStage2WalkFlushPost`) for the empty stream and `stage2Post_of_staging_loop`
  (above) for the loop, modulo the same loop step.

`walkPremises_of_staging` is the producer from the payload groups to `WalkPremises`: the
two bundles are `walkContinueFacts_of_payload` and `walkLoopEnd_of_payload` applied to
those groups, so what the conditional still takes is rows about the document and the call
environment rather than a `∀ G` bundle.  The `stage2WalkCompletes_of_staging` above takes
the same groups, and `JsonStage2WalkFlushPost`'s `stage2WalkObligation_of_staging` composes
the two.

The honest statement of the top level, then, is **not** a change to
`stage2WalkObligation_of_staging`'s conclusion: it is the pair of the completion from
`WalkPremises` and the post from the two staging arms, both already in the tree, at the six
payload groups.  What the groups name is a tier of rows about the document and the call
environment — the continuing arm's per-class evidence and the last entry's arm — and not
the terminal post's numbers, which report the invariant's own word. -/

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkCompletes_of_staging
/-- info: 'LeanLLVM.Refinement.WalkScope.stage2Post_of_staging_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.stage2Post_of_staging_loop
#print axioms LeanLLVM.Refinement.WalkScope.WalkLoopEnd.merge
#print axioms LeanLLVM.Refinement.WalkScope.WalkLoopEnd.refuse
#print axioms LeanLLVM.Refinement.WalkScope.WalkLoopEnd.dispatch

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_of_continue
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopEnd_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStep_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushAt_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkPremises_of_staging

end WalkScope
end LeanLLVM.Refinement
