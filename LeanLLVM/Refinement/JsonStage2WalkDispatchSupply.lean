/-
# The walk's supply, as one named predicate per level

`WalkContinueFacts` and `WalkLoopEnd` (`JsonStage2WalkPremisesOfStaging`) are the loop's
two supplies: a `∀` over head states of an **arm** — `HcontArm`, `LastEntryArm` — each arm's
constructor carrying its own class's premises.  This module states the residual table's
rows (`JsonStage2WalkDispatchResidual`) as one named predicate per level, grouped by the
kind the table gives them, and proves the class paths the payload's own rows reach.

## The groups

Each payload has three groups:

* `lane` — the document's lane facts and the words the walk's own blocks have left at the
  head: the root slot's word, the next entry's position word and its read, the entry's
  extent, the log's two words and the decoded length; and, as `defaultLane`, the default
  arm's own row — the next entry's word and read, the bound's compare, and the byte before
  the entry's end with its three scan-free pivot bits, which every head-switch class's
  chain reads (`JsonStage2WalkDispatchDefaultLane`);
* `abi` — the callee preconditions and answers at each call site's staged argument list:
  the openers' value-position call, and the standalone string's value-position and body
  calls.  Nothing here is a callee's model: the contract is what turns a precondition into
  an answer;
* `trav` — the traversal's row: the document's scan visits, which the run class reads.

None of them holds a bundle (`HcontFacts`, `HcontCleanupFacts`, `HcontScalarFacts`,
`RunFacts`, `HstringFacts`, `HlastResidue`, `HlastFacts`) or an arm (`HcontArm`,
`LastEntryArm`), and none holds a segment: a segment is a run equality, not a fact about a
document and a call environment.

## What the payloads reach, and the row each remaining class needs

The rows below are `JsonStage2WalkDispatchResidual`'s, by class, with the field the payload
does not hold and the reason:

| class | row | why the payload does not hold it |
|---|---|---|
| `.containerOpen`, `.openAtCap`, `.containerOpenRefuse`, `.closeWithOpen`, the four zero refusals, `.commaAboveZero`, `.colonAboveZero` | none — `abi.openCall` (the call's row at the root slot's witness word) and the invariant's own cells | proved below (`…_of_payload`) and in `hcontArm_of_derivedClass`; the payload's `openCall` carries the witness and no answer, and the dispatch splits on it (`s2ValuePos_ret_zero_or_one`) |
| `.twoEntry` | none — `lane.string` and `abi.string` | the class's producer takes exactly these rows plus the invariant — **at depth zero**, which is `strPath8`'s parameter and not a field of the bundle: at a positive depth the same byte has its own arms (the row below) |
| `.ws` | `HcontFacts`'s `hTail`, and of the traversal only the visited byte's class | the tail starts at a *landing* whose index is the run's stop, and the stop is the run's own count; the round, the byte's read and the token's register are produced (`JsonStage2WalkRevolutionScanRound`), so the traversal enters as one document row rather than as its three `∀`-forms |
| `stringOpener` at `%sp ≠ 0` | **the route's segment, not a class row** | the class is `HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`.  Its own facts are derived — the byte from `cont_reg8`, the two stack bytes at `%sp - 1` from the carry's maps and `WalkInv.tyBytes`/`stBytes`, and the value-position staging (`stringOpenAboveZero_pre_of_inv`) — so what the producers take is the merge's counted segment (`hcontArm_stringOpenAboveZeroMerge_of_staging`) or the refusal's witness, which `stringDeepRefuse_at` composes from `if.end245.i`'s state in two links |
| `.cleanup` | **none, at the continuing head**: the class's document row (`HcontCleanupDoc`) | **closed**: `hcontArm_cleanup_of_rows` (`JsonStage2WalkDispatchSeamRows`) takes the document row, the lane's root word and the seam's three call rows, and produces the arm — the seventeen-link chain (`hcontSpan17_of_doc`), the seam's invariant (`contTailStartInv_of_doc`), its five environment cells, the predecessor's `phi` with the literal `0` it selects, and the root slot's word across the seam's three token-record stores are all theorems.  `hcontArm_cleanup_of_calls` remains as the same arm at the seam's cells stated explicitly, and `emptyTailSeg_of_calls` composes the three links.  The two `contTailStart_*` cells are that module's `contTailStart_ee`/`contTailStart_cond` |
| `.scalar` | the empty tail's three calls at the *continuing* route's seam | **the tail's producer is now `scContTail_of_calls`** (`JsonStage2WalkDispatchSegments`): the seam is `scSeamS`, its two test cells are that seam's own peels (`scSeam_ee`, `scSeam_cond`, `JsonStage2WalkHcontScalar`), and `emptyTailSeg_of_calls` composes the three calls at them.  What remains is the arm-level assembly that puts those rows into `HcontScalarFacts` — the bundle's other fields plus the call rows — not a missing cell.  **Closed** by `hcontArm_scalar_of_rows`/`walkDispatch_at_scalar_of_rows` (`JsonStage2WalkDispatchScalarRows`), which take the document row (`HcontScalarPrefix`), the lane word and its read, the three call rows and the class's two agreements — the kind literal `7` and the root slot's word — and produce the arm; the root transport is `scSeam_rootRead` |
| `.letters`, `.fLetter` | the head's chain to `if.else387.i` | **per head-switch class, and now one theorem per class**: `JsonStage2WalkDispatchLettersHead` factors the chain into the **suffix** every default class shares — `sw.default.i`, the count test's succeeding arm, the bound's `phi`, the whitespace check, the byte's three pivots and the token's end, eight links at *any* state at `sw.default.i` (`contDefaultSeg`) — and the class's **prefix**: `.defaultValueLow`'s three links (`contLowHeadSeg`, eleven in all — the low bytes and every byte above `127`), and `.defaultValueMid`/`.otherValue`/`.defaultValueBracket`/`.defaultValueBracketHigh`'s four (`contMidHeadSeg`, `contOthHeadSeg`, `contBrkHeadSeg`, `contBhHeadSeg`, twelve each).  The arm's field is the class's **count**: `HcontArm.letters`/`.fLetter`/`.classC` take `{nH}` with `hnH : nH ≤ 12` (and the `LastEntryArm` twins `hnH : nH ≤ 11`), which the compositions (`lettersCleanupMerge_at`, `fCleanupMerge_at`, `classCMerge_at`) already took, so the class's chain feeds the constructor at every class.  The chain's *cells* are the payload's now: `HcontLane.defaultLane` carries the next lane's word and read, the bound's compare and the byte before the entry's end with its class, and `JsonStage2WalkDispatchDefaultLane` derives the chain at five of the six head-switch classes (`lowHeadChain_of_lane`, `midHeadChain_of_lane`, `othHeadChain_of_lane`, `brkHeadChain_of_lane`, `bhHeadChain_of_lane`; the sixth, `.defaultValueBrace`/`124`, has its chain `contBrcHeadSeg` and still owes its `_of_lane` producer); the three-link tail is produced by `JsonStage2WalkDispatchLettersRows`: the seam's invariant is `lettersSeamInv_of_chain`/`fLetterSeamInv_of_chain`, its cells `lettersSeamCells_of_chain`/`fLetterSeamCells_of_chain` (the pair `contSeamMid_ee`/`contSeamMid_cond`, the root word `contSeamMid_rootRead`), and the tail `emptyTail_of_cells`, so `hcontArm_letters_of_rows`/`hcontArm_fLetter_of_rows` take the call rows and the kind-literal agreement alone |
| `.classC` | the byte's own span | **exposed**: `classCSpan_at` produces a span at the arm's endpoint from the class's `slt %8 110` bit alone (the upper bound is not a premise: `126`/`127` take the same leaf), and `classCHeadSpan_at` composes it with the head's twelve at `12 + nS`.  The arm's `hTail` is stated at the span's *endpoint*, and the endpoint is one of four named states (`ClsS413T`/`ClsS413F`/`ClsS58T`/`HeadS413`), so its seam cells (`HcontSeamCells`: the `phi`, the four pointers, the root word and the two test cells) are **produced** at each (`classCSeamCells_56True` … `…_58Else`, `JsonStage2WalkDispatchClassCLeaves`) and the three-link tail from them; the four arms take the chain, the leaf's bits, its call group and the root word's agreement.  The span is derivable where the endpoint is named, and is the arm's field otherwise.  Its bytes' head-switch classes are `.defaultValueBracketHigh` (`110 … 122`, `contBhHeadSeg`'s twelve) and `.defaultValueBrace` (`124`, `contBrcHeadSeg`'s twelve: `NodeBlock19 → NodeBlock17 → LeafBlock13 → sw.default.i` then the suffix's eight), so every byte of `[110, 125]` the letters arm does not take has its chain and `.classC`'s `hHead` takes it at `nH ≤ 12`. |
| `.run` | `RunFacts` and its four segments | **composed at the whitespace class, and now at any class's check state**: `HcontRunFacts` is the run's bundle stated at the check state itself — the stop, the landing byte and its seam test, the tail, the landing and the traversal — and `contWsRunF` derives the segment at **any** such state, so the class-C route's `contLandS` is its instance (`hcontRunFacts_of_contFacts`) and no longer its only one.  `JsonStage2WalkDispatchRunHead`'s `wsRunHeadAt`/`wsLandingSegAt` build the head and the landing from the bundle, and `runFacts_of_runBundle` the **whole** `RunFacts`, at `nPre ≤ 8`; `runFacts_of_defaultClass` is the six default classes' producer — the class's prefix to `sw.default.i` plus `contSwToLandSeg`'s four, the bundle, and the class's own span.  At `126`/`127` `runFacts_of_wsFacts` remains the instance, and no `RunFacts` field is a supply there.  What remains is the bundle's *fields* at each class (the payload's document and traversal rows), not a composition |
| the last entry's `.highByte` | none — `HlastLane.tail` and `HlastAbi.highByte` | proved below: the residue `HlastResidue` is *built* from the two groups (`lastEntryArm_highByte_of_payload`), so the bundle is constructed, not assumed |
| the last entry's `.scalar` | the three calls at the scalar route's seam | `JsonStage2WalkDispatchScalarOfStaging` states the producer; its call rows are at the scalar route's own seam state, which the payload's last-level `abi` group does not reach |
| the last entry's `.letters`, `.fLetter`, `.classC`, `.run` | the head's eleven links and the listed spans | **closed**: `contDefLastSeg` (`JsonStage2WalkDispatchLettersHead`) states the last entry's seven-link suffix at any state at `sw.default.i` — the failing count test, the bound's `%4`, the whitespace check, the byte's three pivots and the token's end — and `contLastLowHeadSeg` … `contLastBrcHeadSeg` join it to each class's prefix (`contLowToDefault` … `contBrcToDefault`, counted chains of three or four links), giving **ten** links at `.defaultValueLow` and **eleven** at the other five classes.  `hlastTailSeg` is the high-byte class's sixteen links and is not any of them |

So the answer this module gives to "is a bundle still a hypothesis" is: **no bundle is
assumed by the payloads or by the paths proved here; the classes listed above take a named
row (a segment, a traversal `∀`, or a bundle structure not yet split), and the field and
the reason are named row by row in the table above.**

## What the segments' exposure moved

`hcontHeadSeg12` (`JsonStage2WalkRevolutionPrefix`) is the continuing head's **twelve**
links, the high-byte class's, and `hcontToSpan` is now its composition with the class-C
span rather than a second copy of the head's path.  `JsonStage2WalkDispatchCleanupSpan`
applies the twelve to `HcontCleanupFacts`'s own fields (`hcontHeadSeg12_of_cleanup`),
composes them with the span at seventeen (`hcontSpan17_of_cleanup`) and gives that
composition its consumer, `hcontPrefixCleanupSeg` — which `walkRevolutionMergeSeg`
(`JsonStage2WalkRevolutionSeg`) reads for the scan-free arm's twenty links.  So no exposed
statement of that chain is without a consumer, and the twelve appear once.

`JsonStage2WalkDispatchSegments` states the class-C span's one interface and the tails:

* `classCSpan_at` — the class-C span at the arm's endpoint, one interface over the four
  leaves, and `classCHeadSpan_at` at `12 + nS`;
* `runSegmentsAt` — the run's four segments at their own counts, head included — its
  counted composition's consumer is `runToLatchSeg_at`;
* `emptyTailSeg_of_calls` — the empty tail's **three** links from the three callees' rows,
  at any carry whose block is `if.then413.i`.  `.cleanup` now consumes it
  (`hcontArm_cleanup_of_calls`, `walkDispatch_at_cleanup_of_calls`), the last entry's tail
  is its instance (`hlastTail_of_calls`), so is the last entry's scalar route
  (`scalarTail_of_calls`), and so is the continuing scalar route (`scContTail_of_calls`, at
  `scSeamS`'s own two cells).

The two rows this round set out to retire are **statements now**: the letters class's head
chain is one theorem per head-switch class (`JsonStage2WalkDispatchLettersHead`, above), and
the run class's head is composed at the whitespace class with the whole `RunFacts` built
from `HcontFacts` (`JsonStage2WalkDispatchRunHead`, above).

The first of the three obstacles is **retired**: the default arms' head field is the
class's counted segment.  `HcontArm.letters`/`.fLetter`/`.classC` take `{nH : Nat}` and
`hnH : nH ≤ 12`, and the `LastEntryArm` twins take `hnH : nH ≤ 11`, so
`.defaultValueLow`'s eleven-link continuing chain and ten-link last chain feed the same
constructor as the four-pivot classes' twelve and eleven.  The compositions already took
the pair, so the enum changed and every consumer passes `hnH`;
`JsonStage2WalkDispatchLettersDomain`'s `\xC8 0` exhibit is re-pointed at its eleven-link
chain.

What that does **not** yet give is the bundle theorems
`walkContinueFacts_of_payload`/`walkLoopEnd_of_payload`, and the remaining rows are named
exactly here.  None is a missing segment.

| row | what it is | what it needs |
|---|---|---|
| the default arm's document cells | the next entry's position word and its read, the bound's compare, and the byte before the entry's end with its three pivot bits | **closed**: `HcontLane.defaultLane` carries them and `JsonStage2WalkDispatchDefaultLane` turns them into the class's head chain at all five head-switch classes (`lowHeadChain_of_lane`, `midHeadChain_of_lane`, `othHeadChain_of_lane`, `brkHeadChain_of_lane`, `bhHeadChain_of_lane`) and into the three arms (`hcontArm_letters_of_lane`, `hcontArm_fLetter_of_lane`, `hcontArm_classC_of_lane`) with their dispatches.  The chain's other cells are derived through the class's prefix and the suffix's first bind; the document byte is transported by `contMidS_docByte`.  What remains for those arms is the tail's three calls and `.classC`'s span |
| the default arm's tail and span | the three callees' rows and the class-C leaf | the payload's `abi` group carries the openers' and the string's calls, not the tail's; `emptyTailSeg_of_calls` produces the segment from the three callees' preconditions and answers, which the staging supplies at the seam's landing.  `.classC`'s span is `classCSpan_at`'s at the byte's own leaf |
| the run's bundle at each default class | `RunFacts` at the six default head classes | **closed, apart from the bundle's own supply**: the run is stated once at an arbitrary check state (`HcontRunFacts`, `contWsRunF`), so the class-independent part is no longer a per-class restatement: `runFacts_of_runBundle` builds the whole bundle from it at any class's chain to the check state at `nPre ≤ 8`, and `runFacts_of_defaultClass` is the six classes' one producer — the class's prefix to `sw.default.i` (`nq ≤ 4`), `contSwToLandSeg`'s shared four and the bundle, with the class's own span (`.defaultValueBracketHigh`/`.defaultValueBrace`/`115`'s `LeafBlock58` arm, `.defaultValueLow`/`.defaultValueMid`/`.otherValue`'s letters span).  What the row still needs is the bundle's *fields* at each class's check state — its stop `k`, the landing byte, the tail's three callee rows and the traversal — which is the payload's supply, named in the next row |
| the run's bundle fields | `HcontRunFacts` at `contLandOut (contMidS C q5 …) v b35` | the class's own head bundle is not the run's: `HcontFacts` is stated at the high-byte route's `contLandS`, and its `hClass` is the byte's class.  The fields the check state supplies are the first six (`hInv`, `%35`, `%idxprom.i`, `%cond350.i`, `hugt`, `h8c`), which the class's prefix and `contSwToLandSeg` derive (`contLandS_idx`/`contLandS_cond` are the class-C instance of the same peels); the rest — the stop, the class, the seam's byte test, the tail, the landing and the traversal — are the document's and the staging's, so they enter as the payload's rows.  No field is a segment |
| the last entry's default arms | a per-class last-entry chain, and the last level's run bundle | **the chain is closed, the run bundle is not**: `JsonStage2WalkDispatchLettersHead` states the last entry's suffix once (`contDefLastSeg`, seven links: the failing count test `%inc.i ≥ %nep`, the bound's `%4`, the whitespace check, the byte's three pivots and the token's end) and one counted chain per prefix class (`contLastLowHeadSeg` at ten links, `contLastMidHeadSeg`/`contLastOthHeadSeg`/`contLastBrkHeadSeg`/`contLastBhHeadSeg`/`contLastBrcHeadSeg` at eleven).  `hlastTailSeg` is the high-byte class's sixteen links and is not any of them.  What the row still needs is the last level's **run** bundle: `lastEntryArm`'s `.run` constructor takes `RunLastFacts`, whose `hHead`/`hSpan` are segments, so no payload row can stand in for it (`runLastFacts_of_staging` remains its producer at the staging) |
| `walkContinueFacts_of_payload` | `HcontPayload` → `WalkContinueFacts` | the rows above at every arm; the payload must not hold an arm or a segment, so the class case over `HcontClass.complete` runs each class's producer.  The default arm's chain is in hand; its tail, `.ws`/`.cleanup`'s call rows and `.scalar`'s seam are the rows still listed above.  The class case is complete: the positive-depth opener's `%sp ≠ 0` states are `HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`, whose class facts the invariant supplies and whose row is the merge's counted segment (`JsonStage2WalkDispatchHcontStringDeep`), with `.twoEntry`'s `C.sp = 0` beside them.  What the theorem still needs is the document rows, not an arm |
| `walkLoopEnd_of_payload` | `HlastPayload` → `WalkLoopEnd` | the last entry's rows above, and the terminal log words `WalkLoopEnd.merge`/`.refuse` compose |

A `walkContinueFacts_of_payload` stated over a payload carrying those groups would be a
class case over `HcontClass.complete` with every arm's producer in hand.  What this module
will not do is state it over a payload that quietly holds the arms themselves.

## The seam's calls and the run's rows

`JsonStage2WalkDispatchSeams` states the two groups the rows above were waiting on, and the
producer the scan arm needed:

| statement | what it is |
|---|---|
| `HcontSeamCalls G C s` | **the seam's three calls as one group**: the value-position call, the scalar call's emit arm and the copy call, each with its precondition at the staged argument list, its outcome and the memory it reads and leaves.  It carries the kind literal `cA` and the root-done word `rdv` because the memories mention them; the seam's own cells are the state's, not the group's |
| `HcontSeamAbi G` | the group at each seam, one `∀`-field: the continuing run class's `if.then413.i` (at `contWsTailStart`) and the last entry's (at `hlastTail`) |
| `scanTailSeg_of_calls` | **the scan arm's tail from those rows**: `consumerTailSegAt`'s three links at `TailCarryScan C ev`, ending at the scan's entry, returning the record the scalar call appends.  `emptyTailSeg_of_calls`'s twin, and the piece it does not cover: the empty arm's equation `%ee.1.i = %cond350.i` becomes the scan arm's strict inequality and span |
| `hcontScanTail_of_calls`, `hcontScanTail_at` | that producer at the run class's seam — the `∃`-form (`Facts`'/`RunFacts`' `hTail`) and the record-pinned form |
| `HcontRunRows G C sl b35 ix v k x1` | **the run's rows at a class's check state**: `HcontRunFacts` minus its `hTail` field — the check state's cells, the whitespace stop and its class, the entry's span, the landing's byte and its three reads, and the traversal's `hround`/`hbyte` (the old `hguard` is gone, and the round and the read are produced by `JsonStage2WalkRevolutionScanRound`).  It carries the seam's call group and the record they appended, because the landing's rows are stated at `contWsEntry`, which takes the answers |
| `hcontRunFacts_of_rows` | `HcontRunFacts` from the rows and the seam's cells: every field but the tail is the rows', and the tail is `hcontScanTail_at`.  So `runFacts_of_runBundle`'s input is segment-free |

What is still not stated is the pair of bundle theorems.  They are **not** blocked by a
segment: each arm's chain, span and tail is producible from rows (`lowHeadChain_of_lane` …
`bhHeadChain_of_lane`, `classCSpan_at`, `contSwToLandSeg`, `emptyTailSeg_of_calls`,
`hcontScanTail_at`).  They are blocked by the payload's **per-class document rows**: the
class case over `HcontClass.complete` needs `HcontFacts`'s and `HcontScalarFacts`'s
non-callee fields at every head state (the byte before the entry's end with its class, the
entry lane and its order, the whitespace stop with its per-index `∀`, the log's two
words), the refusals' `%idxprom.i`/`%e` cells, and — for the last level —
`RunLastFacts`'s rows.  The continuing payload carries the openers' and the string's only,
so `walkContinueFacts_of_payload` would be a class case whose evidence classes are missing,
and a theorem stated with them added would take the classes' bundles under another name.

**One class is now closed end to end, and its shape is the other classes' target.**
`JsonStage2WalkDispatchSeamRows` produces `.cleanup`'s arm from the class's document row,
the lane's root word and the seam's three call rows alone: the seventeen links, the seam's
invariant, its five environment cells, the predecessor's `phi`, and the root slot's word
across the seam's three token-record stores are theorems there
(`hcontSpan17_of_doc` … `hcontArm_cleanup_of_rows`).  Nothing that class's arm establishes
is assumed by its producer, and the two seam cells it also reads are
`JsonStage2WalkHcontFactsOfStaging`'s `contTailStart_ee` and
`JsonStage2WalkDispatchSegments`'s `contTailStart_cond`.  The other classes' rows are the
same kind; what separates them is the seam the tail starts from and, for `.ws`/`.run`,
the scan's traversal `∀`s, which no theorem produces yet.

## The closure claim

Its statement is unchanged: `stage2WalkObligation_of_premises`
(`JsonStage2WalkAssembly`) takes `WalkPremises` and the record's post rule and no bundle,
and `walkPremises_of_staging` is its only producer.  What this module adds is the payloads
`stage2WalkObligation_of_payload` would be stated with, and the row map above that says
which fields stand between the payloads and `WalkPremises`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchResidual
import LeanLLVM.Refinement.JsonStage2WalkDispatchSpansOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosersOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchZeroOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchStringOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupOfStaging
import LeanLLVM.Refinement.JsonStage2WalkHcontFactsOfStaging
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing level's rows -/

/-- **The standalone string's lane facts**, at the class's own staging.  `A` is the log's
arena-base word and `Cc` its base word; `outn` is the decoded length the body call writes
at `%next0 + 20`. -/
structure HcontStringLane {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  bs : List UInt8
  hreadLane : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some bs
  hq : bytesToNat bs = entryPos G (C.k + 1)
  rd : BitVec 32
  hreadRoot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4)
  A : BitVec 64
  hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8)
  Cc : BitVec 64
  hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8)
  outn : Nat
  houtn : readBytes s.mem (G.next0 + 20) 8 = some (wordBytes 8 outn)
  hcur : C.alen ≤ G.ndst0 + (contIx G C).toNat
  hwin : C.alen + (entryPos G (C.k + 1) - (contIx G C).toNat - 1) ≤ G.n

/-- **The standalone string's two call rows.**  `hpreV` and `hpreS` are the callees'
preconditions at the staged argument lists; `hxv` and `hy` their answers; `hR8` is
`NodeBlock31`'s test on the body's answer, which the accepting arms satisfy. -/
structure HcontStringCalls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (rd : BitVec 32) (A : BitVec 64) : Type where
  hpreV : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next
  xv : BitVec 32
  hxv : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r → r.ret = .int 32 xv
  hbranch : evalICmp .ne xv (BitVec.ofNat 32 0) = 1
  hpreS : s2StringBodyPre
    [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
     .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
     .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
     .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next
  y : BitVec 32
  hy : ∀ r, stage2Calls stage2SubCalls "s2_string_body"
    [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
     .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
     .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
     .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r → r.ret = .int 32 y
  hR8 : evalICmp .slt y (BitVec.ofNat 32 1) = 0

/-! ### The lane's five reads, and which of them the tree states

`HcontStringLane` reads five words at the head state.  Four follow from clauses `WalkInv`
already carries, and the fifth does not:

* the **next entry's position word** is the geometry's `entries` table transported to the
  state by the frame's silence over the entry stream and its `k + 1`-th lane
  (`walkReadBytes_entryPos_word`);
* the **root slot's word** is `WalkInv.root_slot`'s four present bytes read back as a word
  (`walkReadBytes_rootSlot_word`).  The clause states presence and not the value, so the
  lane's `rd` is a witness: nothing in the invariant pins it, and no consumer needs it
  pinned — `s2ValuePosPre` takes the word it is handed;
* the **log's arena word** is `WalkInv.log_alen`'s read at `%z + 48`
  (`walkReadBytes_logArena_word`), whose *value* the clause bounds rather than names;
* the **log's capacity word** is `WalkInv.log_acap` read as `dstcap` outright
  (`walkReadBytes_logCap_word`).

The fifth, the **decoded length** at `%outn.i`, is statable as a clause but not produced by
this module.  The slot is one of the four `alloca` slots `WalkInv.owned` deliberately omits
— its docstring records that their presence is false at the loop head — so the eight bytes
at `G.next0 + 20` are named by no clause, and a clause naming them is an invariant edit
carried through every construction site, not a dispatch row.  Its *value* is the previous
iteration's body call: `s2StringBody_outn_le` (`JsonStage2Helpers`) turns the accepting
forms of `stage2StringBody` into `∃ on, readBytes m outn 8 = some (wordBytes 8 on) ∧ on ≤
len.toNat` at the answered memory, and `strPath9`/`strPath10`
(`JsonStage2WalkDispatchWitnessString`) transport it across the private slot's write to
`r.mem`.  What is missing is the carrier: neither `s2StringBodyPre` nor the body's answer
(`HcontStringCalls.hy`) mentions the slot, so the word produced at the answer has no
theorem carrying it to the next head where `HcontStringLane.houtn` is read.  So the lane's
row is one slot's presence at the head and one postcondition at the call, and the other
four reads are proofs.
-/

/-- **The next entry's position word**, from the entry stream and the frame.  `G.entries`
is the table at the staged memory; `WalkInv.frame` and `entry_outside` carry the read to
the state, and `readLanes32_nth` names the lane's word as the entry's own position. -/
theorem walkReadBytes_entryPos_word {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) {k : Nat} (hk : k < G.nep) :
    ∃ bs : List UInt8, readBytes s.mem (G.ep + k * 4) 4 = some bs ∧
      bytesToNat bs = entryPos G k := by
  obtain ⟨-, hget⟩ := readLanes32_nth (m := m0) (addr := G.ep) (n := G.nep)
    (l := G.ent) G.entries
  obtain ⟨q, bs, hqmem, hread0, hbs0⟩ := hget k hk
  refine ⟨bs, ?_, ?_⟩
  · rw [show G.ep + k * 4 = G.ep + 4 * k from by rw [Nat.mul_comm]]
    rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame)
      (a := G.ep + 4 * k) (n := 4)
      (fun i hi => hInv.entry_outside (by omega) (by omega))]
    exact hread0
  · rw [hbs0, entryPos, List.getD_eq_getElem?_getD, hqmem, Option.getD_some]

/-- **The root slot's word.**  `WalkInv.root_slot` is presence over the slot's four bytes;
four present bytes are a word (`natToBytes_bytesToNat`, with the value below `2 ^ 32`
because four bytes are).  The clause fixes no value: the witness is the memory's own. -/
theorem walkReadBytes_rootSlot_word {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) :
    ∃ rd : BitVec 32, readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4) := by
  obtain ⟨vs, hvs⟩ := hInv.root_slot
  have hlen : vs.length = 4 := walkReadBytes_length hvs
  refine ⟨BitVec.ofNat 32 (bytesToNat vs), ?_⟩
  rw [walkToNat_ofNat32 (bytesToNat_lt_32 hlen), ← hlen,
    JsonEntrySteps.natToBytes_bytesToNat, hlen]
  exact hvs

/-- **The depth-zero value-position answer decides the root word.**  The callee's contract
is `s2ValuePosPost`: its return is the model's `stage2ValuePos`, which at depth zero is
`if rootDone = 0 then 1 else 0`.  So an answer of `1` at depth zero is possible only when
the word the caller passed is `0` — the fact `if.then.i`'s `load` supplies to the call.

This is the *contract* side of the root slot's zero: it turns the word into a consequence
of the answer (`hret`), not a clause about the memory.  It does not by itself discharge
`HcontLane.root`, because the arm's argument list names the literal `0` (`HcontOpenCall`)
and the segment's `openTailSeg` reads the slot as a memory fact; the arm would have to carry
the slot's witness word for this to produce it.  At a positive depth the answer does not
depend on the word at all, so nothing there can produce a value. -/
theorem s2ValuePos_rootWord_of_answer {mem : Mem} {next : Nat} {sp rd : BitVec 32}
    {ct cs : Nat} {r : CallOutcome}
    (hsp : sp.toNat = 0)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    rd.toNat = 0 := by
  rw [s2ValuePos_reply] at hcall
  have h0 : stage2ValuePos mem sp.toNat rd.toNat ct cs =
      some (if rd.toNat = 0 then 1 else 0) := by
    simp only [stage2ValuePos, hsp, ↓reduceIte]
  rw [h0] at hcall
  have hr : (⟨.int 32 (BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0)), mem, next⟩ :
      CallOutcome) = r := Option.some.inj hcall
  rw [← hr] at hret
  have hv : BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0) = BitVec.ofNat 32 1 := by
    simpa using hret
  by_contra hne
  have hz : (if rd.toNat = 0 then 1 else 0) = 0 := by rw [ite_eq_right hne]
  rw [hz] at hv
  exact absurd hv (by decide)

/-- **The value-position model's answer is a bit.**  Each arm of `stage2ValuePos` returns
`if … then 1 else 0`; the negated arms return `none`, which the hypothesis excludes. -/
theorem stage2ValuePos_lt_two {mem : Mem} {sp rd ct cs : Nat} {v : Nat}
    (hv : stage2ValuePos mem sp rd ct cs = some v) : v < 2 := by
  unfold stage2ValuePos at hv
  split at hv
  · have h := (Option.some.inj hv).symm
    rw [h]
    split <;> (try split) <;> omega
  · split at hv
    · have h := (Option.some.inj hv).symm
      rw [h]
      split <;> (try split) <;> omega
    · cases hv

/-- **The answer of a value-position call is `1` or `0`.**  The callee returns the model's
bit, so every invariant state's call settles into one of the two routes: `1` for the
openers' merge (`if.end.i`) and `0` for the refusal (`if.then16.i`).  This is what makes
the byte class `91`/`123` total over the invariant's states rather than only over its
bytes. -/
theorem s2ValuePos_ret_zero_or_one {mem : Mem} {next : Nat} {sp rd : BitVec 32}
    {ct cs : Nat} {r : CallOutcome}
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next = some r) :
    r.ret = .int 32 (BitVec.ofNat 32 1) ∨ r.ret = .int 32 (BitVec.ofNat 32 0) := by
  rw [s2ValuePos_reply] at hcall
  cases hv : stage2ValuePos mem sp.toNat rd.toNat ct cs with
  | none =>
      rw [hv] at hcall
      cases hcall
  | some v =>
      have hr : r = ⟨.int 32 (BitVec.ofNat 32 v), mem, next⟩ :=
        Option.some.inj (hcall.symm.trans (by rw [hv]; rfl))
      rw [hr]
      have h2 := stage2ValuePos_lt_two hv
      have hb : v = 0 ∨ v = 1 := by
        rcases v with _ | _ | n
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      rcases hb with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h])

/-- **A store inside the token record leaves the root slot's word alone.**  The record ends
at or below `G.next0` (`WalkStage.sevenEnd`) and the root slot is four bytes at
`G.next0 + 8`, so a store whose extent is inside the record (`start`'s plus the payload's,
both bounded by the record's extent) is outside the slot's range. -/
theorem readBytes_rootSlot_tokWrite {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {m : Mem} {start len : Nat} {v : List UInt8}
    (hstart : start + len ≤ C.stage.tok + stage2TokenExtent) (hlen : v.length = len) :
    readBytes (writeBytes m start v) (G.next0 + 8) 4 = readBytes m (G.next0 + 8) 4 := by
  refine walkReadBytes_writeBytes_outside (m := m) (v := v) (start := start)
    (addr := G.next0 + 8) (n := 4) ?_
  refine Or.inr ?_
  have h := C.stage.sevenEnd (C.stage.tok, stage2TokenExtent) (by simp [stage2StagedWrites])
  simp only [stage2TokenExtent] at h hstart
  omega

/-- **What `s2_after_value` writes at the root slot, at depth zero.**  The contract's post
is the model's `stage2AfterValue`, whose depth-zero arm is
`writeBytes mem rootDone (wordBytes 4 1)`.  So the slot holds **`1`**, not `0`: the callee
never writes the zero `entry`'s initial store left.  This is why c11's zero cannot be a
consequence of this contract — a head that has passed through a depth-zero call has `1`
there, and the value-position call's answer is what distinguishes the two. -/
theorem s2AfterValuePost_rootSlot_at_zero {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {mem : Mem} {next : Nat} {sp : BitVec 32} {r : CallOutcome}
    (hpost : s2AfterValuePost [.int 32 sp, .ptr (G.next0 + 8), .ptr C.stage.ctype,
      .ptr C.stage.cst] mem next r)
    (hsp : sp.toNat = 0) :
    readBytes r.mem (G.next0 + 8) 4 = some (natToBytes 1 4) := by
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  rw [hmem]
  unfold stage2AfterValue at hm
  rw [hsp, ite_eq_left rfl] at hm
  obtain rfl := Option.some.inj hm
  have h := readBytes_writeBytes_same mem (natToBytes 1 4) (addr := G.next0 + 8)
  rwa [show (natToBytes 1 4).length = 4 from natToBytes_length 1 4] at h

/-- **What `s2_after_value` leaves at the root slot, above depth zero.**  The positive-depth
arm writes one byte of the state stack at `%cst.i + (%sp - 1)`, and the stack's staged extent
ends at or below `G.next0`, so the slot is untouched: the word the caller held is the word it
still holds.  Together with `s2AfterValuePost_rootSlot_at_zero` this is the callee's whole
effect on the slot — `0` is not among its writes. -/
theorem s2AfterValuePost_rootSlot_above {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {mem : Mem} {next : Nat} {sp : BitVec 32} {r : CallOutcome}
    (hpost : s2AfterValuePost [.int 32 sp, .ptr (G.next0 + 8), .ptr C.stage.ctype,
      .ptr C.stage.cst] mem next r)
    (hsp : sp.toNat ≠ 0) (hcap : sp.toNat ≤ stage2StackExtent) :
    readBytes r.mem (G.next0 + 8) 4 = readBytes mem (G.next0 + 8) 4 := by
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  rw [hmem]
  unfold stage2AfterValue at hm
  rw [ite_eq_right hsp] at hm
  cases hc : readByte mem (C.stage.ctype + (sp.toNat - 1)) with
  | none => rw [hc] at hm; cases hm
  | some ctv =>
      rw [hc] at hm
      obtain rfl := Option.some.inj hm
      refine walkReadBytes_writeBytes_outside (m := mem)
        (v := [UInt8.ofNat (if ctv.toNat = 1 then 3 else 1)])
        (start := C.stage.cst + (sp.toNat - 1)) (addr := G.next0 + 8) (n := 4) ?_
      refine Or.inr ?_
      have hse := C.stage.sevenEnd (C.stage.cst, stage2StackExtent)
        (by simp [stage2StagedWrites])
      simp only [stage2StackExtent] at hse hcap
      show C.stage.cst + (sp.toNat - 1) + 1 ≤ G.next0 + 8
      omega

/-- **The root slot's word at the last entry's seam.**  The tail's start's stores are all
inside the token record: `cond.end349.i`'s position and gap stores (`%t352.i` and
`%t352.i + 20`), the seam's end store at `%t352.i + 8`, and the tail's three calls' kind
store at `%t352.i + 16`.  The record ends at or below `G.next0` (`WalkStage.sevenEnd`) and
the root slot is four bytes at `G.next0 + 8`, so every one of them misses it: the word the
copy call's argument list carries is the head's, read by `walkReadBytes_rootSlot_word` from
`WalkInv.root_slot`.

The value is the memory's — `rdv` is a witness, not a number.  That is the honest statement
of l1's row: the slot has two writers (`entry`'s initial `0` and `s2_after_value`'s
depth-zero flag `1`, `s2AfterValueBody_contract`), so no clause names its value at the
exhausted count, and no consumer needs it pinned. -/
theorem hlastTail_rootSlot_word {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (cA : BitVec 32) (hInv : WalkInv G C s) :
    ∃ rdv : BitVec 32,
      readBytes (writeBytes (hlastTail C s x inc nep v ix b35).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) := by
  obtain ⟨rd, hread⟩ := walkReadBytes_rootSlot_word hInv
  refine ⟨rd, ?_⟩
  have hmem : (hlastTail C s x inc nep v ix b35).mem =
      writeBytes
        (writeBytes
          (writeBytes s.mem C.stage.tok (natToBytes ix.toNat 8))
          (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4))
        (C.stage.tok + 8) (natToBytes (BitVec.ofNat 64 v).toNat 8) := by
    simp only [hlastTail, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, hlastSeam, seamS,
      seamFin, hlastP35, hlastP39, hlastP41, hlastLand, headEndS, condEnd349OutAt, headAS₅,
      headAS₄, headAS₃, headAS₂, headAS₁, stateAt, State.bind, cells]
  rw [hmem]
  rw [readBytes_rootSlot_tokWrite (C := C) (start := C.stage.tok + 16) (len := 4)
    (v := natToBytes cA.toNat 4) (by simp only [stage2TokenExtent]; omega)
    (natToBytes_length _ _)]
  rw [readBytes_rootSlot_tokWrite (C := C) (start := C.stage.tok + 8) (len := 8)
    (v := natToBytes (BitVec.ofNat 64 v).toNat 8) (by simp only [stage2TokenExtent]; omega)
    (natToBytes_length _ _)]
  rw [readBytes_rootSlot_tokWrite (C := C) (start := C.stage.tok + 20) (len := 4)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4)
    (by simp only [stage2TokenExtent]; omega) (natToBytes_length _ _)]
  rw [readBytes_rootSlot_tokWrite (C := C) (start := C.stage.tok) (len := 8)
    (v := natToBytes ix.toNat 8) (by simp only [stage2TokenExtent]; omega)
    (natToBytes_length _ _)]
  exact hread

/-- **The log's arena word**, at the invariant's own existential: `log_alen` names both
the read and the bound its value sits in. -/
theorem walkReadBytes_logArena_word {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) :
    ∃ A : BitVec 64, readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8) := by
  obtain ⟨a, ha1, ha2, hr⟩ := hInv.log_alen
  have ha : a < 2 ^ 64 := by
    have h1 := hInv.alen_le
    have h2 := G.arenaRoom
    have h3 := G.dstcapLt
    omega
  refine ⟨BitVec.ofNat 64 a, ?_⟩
  rw [walkToNat_ofNat64 ha]
  exact hr

/-- **The log's capacity word**: `log_acap` names it as `dstcap`. -/
theorem walkReadBytes_logCap_word {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) :
    ∃ Cc : BitVec 64, readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8) := by
  refine ⟨BitVec.ofNat 64 G.dstcap, ?_⟩
  rw [walkToNat_ofNat64 G.dstcapLt]
  exact hInv.log_acap

/-- **The openers' call row**: the root slot's witness word and its read, the
predicondition at the argument list the `load` builds, the outcome — and no answer.

**Why the answer is not a field.**  The word `%9` the block loads from the slot is the
call's third argument, and the class fixes no value for it: the slot's writers are
`entry`'s initial `0` and `s2_after_value`'s depth-zero flag `1`
(`s2AfterValuePost_rootSlot_at_zero`, `…_above`), so `0` is not among the callee's writes
and no clause names the word.  The row therefore carries the memory's own word as a
witness and the call at it; the answer is the *state's*, and the dispatch splits on it
into the `1` route (`if.end.i`) and the `0` refusal (`if.then16.i`).  That split is what
makes the byte class total over the invariant's states — `s2ValuePos_ret_zero_or_one` says
the answer is one of the two bits. -/
structure HcontOpenCall {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The word the block's `load` read from the root slot. -/
  rdv : BitVec 32
  /-- The read that names it. -/
  hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  hpreV : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next
  r : CallOutcome
  hcall : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r

/-- **The default arm's document row.**  The next entry's position word and the read that
fetches it, the bound's compare against this entry's index, and the byte before the
entry's end with its three scan-free pivot bits.  A structure rather than a `∃` because a
chain producer reads the witness into data: a `Prop`-valued existential cannot be
eliminated into the `Type` the chain is.  The read is taken at the head state's memory: the
head switch's binds and the suffix's four binds leave memory alone, and the two
token-record stores are outside the document's staged region, so the same row feeds every
class's chain.  The witness is the word the position table holds; the two bounds say it is
the next entry's, above zero and no further than its position. -/
structure HcontDefaultRow {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  v : BitVec 32
  hread : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some (natToBytes v.toNat 4)
  hv1 : 1 ≤ v.toNat
  hvle : v.toNat ≤ entryPos G (C.k + 1)
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) (contIx G C) = 1
  hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 1
  hbne13 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0

/-- **The document's lane facts at a continuing head**: the words the dispatch's own
blocks have already laid down, read at the state the arm is read at.

**The root slot's value is not here.**  The openers read it as the call's third argument,
and the read is a theorem (`walkReadBytes_rootSlot_word`): the slot's presence in
`WalkInv.root_slot` is four bytes, and four present bytes are a word.  Its *value* is the
memory's — `entry` writes the initial `0` and `s2_after_value`'s depth-zero arm writes `1`
(`s2AfterValuePost_rootSlot_at_zero`; above depth zero it leaves the slot,
`…_above`) — so no clause names it and none is owed: the arms carry it as their witness
(`HcontOpenCall.rdv`), and the answer the callee gives at that word selects the arm. -/
structure HcontLane {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The standalone string's lane. -/
  string : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → C.sp = 0 → HcontStringLane G C s
  /-- The default arm's document row. -/
  defaultLane : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontDefaultRow G C s

/-- **The callee preconditions and answers at a continuing head.** -/
structure HcontAbi {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The openers' value-position call. -/
  openCall : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontOpenCall G C s
  /-- The standalone string's two calls, at the lane's own words. -/
  string : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → C.sp = 0 → (rd : BitVec 32) → (A : BitVec 64) →
    HcontStringCalls G C s rd A

/-- **The traversal's row at a continuing head**: the document's own scan visits. -/
structure HcontTrav {m0 : Mem} (G : WalkGeom m0) : Type where
  visits : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → ScanVisits G (entryPos G (C.k + 1))

/-- **The continuing payload**: the residual table's rows, grouped by kind. -/
structure HcontPayload {m0 : Mem} (G : WalkGeom m0) : Type where
  lane : HcontLane G
  abi : HcontAbi G
  trav : HcontTrav G

/-! ### The continuing openers, from the payload

The class's two bytes and two depths: `if.then.i`'s call and the merge's nine links below
the guard, or the same call and `if.end.i`'s taken arm to the copy — and, when the call
answers `0`, its branch to `if.then16.i` and the refusal's six links.  The payload supplies
the call's row at the root slot's witness word; the answer is the state's, and
`s2ValuePos_ret_zero_or_one` splits it, so the class is covered at every invariant state. -/

/-- **The open bracket's continuing dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open91_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hp : HcontPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨rdv, hread, hpreV, r, hcall⟩ := hp.abi.openCall C s hInv hblock hk
  rcases s2ValuePos_ret_zero_or_one hcall with h1 | h0
  · by_cases hsp : C.sp ≤ 519
    · exact HcontArm.dispatch hInv hblock hk
        (hcontArm_containerOpen91_of_staging C s hInv hclass hsp hread hpreV r hcall h1)
    · have h520 : C.sp = 520 := by
        have hcap := hInv.depth_cap
        simp only [stage2StackExtent] at hcap
        omega
      exact HcontArm.dispatch hInv hblock hk
        (hcontArm_openAtCap91_of_staging C s hInv hclass h520 hread hpreV r hcall h1)
  · exact HcontArm.dispatch hInv hblock hk
      (hcontArm_containerOpenRefuse91_of_staging C s hInv hclass hread hpreV r hcall h0)

/-- **The open brace's continuing dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open123_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hp : HcontPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨rdv, hread, hpreV, r, hcall⟩ := hp.abi.openCall C s hInv hblock hk
  rcases s2ValuePos_ret_zero_or_one hcall with h1 | h0
  · by_cases hsp : C.sp ≤ 519
    · exact HcontArm.dispatch hInv hblock hk
        (hcontArm_containerOpen123_of_staging C s hInv hclass hsp hread hpreV r hcall h1)
    · have h520 : C.sp = 520 := by
        have hcap := hInv.depth_cap
        simp only [stage2StackExtent] at hcap
        omega
      exact HcontArm.dispatch hInv hblock hk
        (hcontArm_openAtCap123_of_staging C s hInv hclass h520 hread hpreV r hcall h1)
  · exact HcontArm.dispatch hInv hblock hk
      (hcontArm_containerOpenRefuse123_of_staging C s hInv hclass hread hpreV r hcall h0)

/-! ### The standalone string, from the payload

The class's producer takes exactly the payload's two groups — the lane's words and the two
calls' rows — plus the invariant, so this is the class the payload discharges without a
segment or a residual. -/

/-- **The standalone string's continuing arm, from the payload's rows.**  `hsp0` is the
class's selector (`if.then219.i`'s depth test) and the arm's own, not the payload's. -/
def hcontArm_twoEntry_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (heq34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    (hsp0 : C.sp = 0) (hp : HcontPayload G) :
    HcontArm (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨bs, hreadLane, hq, rd, hreadRoot, A, hreadA, Cc, hreadC, outn, houtn, hcur,
    hwin⟩ := hp.lane.string C s hInv hblock hk hsp0
  obtain ⟨hpreV, xv, hxv, hbranch, hpreS, y, hy, hR8⟩ :=
    hp.abi.string C s hInv hblock hk hsp0 rd A
  exact .twoEntry
    (hstringFacts_of_staging G C s hInv hk heq34 hreadLane hq hreadRoot hpreV hxv
      hbranch hcur hreadA hreadC hpreS hwin hy houtn)
    hsp0 ⟨⟩ hR8

/-- **The standalone string's continuing dispatch, from the payload's rows.** -/
theorem walkDispatch_at_twoEntry_of_payload {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (heq34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    (hsp0 : C.sp = 0) (hp : HcontPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_twoEntry_of_payload hInv hblock hk heq34 hsp0 hp)

/-! ### The last entry's rows and openers -/

/-- **The last byte's class**: the document's content at `%4 - 1`, whose three pivots take
`if.end372.i` straight to the seam. -/
structure HlastTailLane {m0 : Mem} (G : WalkGeom m0) : Type where
  hb13 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 1
  hbne13 : evalICmp .eq (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 13) = 0

/-- **The high-byte class's three calls**, at their staged argument lists: the
value-position call, the scalar call with the append's record, and the copy call.  These
are the rows `JsonStage2WalkDispatchWitnessHlast`'s `HlastResidue` carries, restated as one
group. -/
structure HlastHighByteAbi {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  rdv : BitVec 32
  xA : BitVec 32
  hreadT : readBytes
    (writeBytes (hlastTailNat C s).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes rdv.toNat 4)
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
     .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
    (writeBytes (hlastTailNat C s).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (hlastTailNat C s).next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
     .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
    (writeBytes (hlastTailNat C s).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (hlastTailNat C s).next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  hzread : readBytes
    (writeBytes (hlastTailNat C s).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev)
  hpre₂ : s2ScalarValuePre
    [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
     .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
     .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next = some r₂
  hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1)
  hev64 : G.ev < 2 ^ 64
  hpre₃ : s2AfterValuePre
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
     .ptr (TailStartC C).stage.ctype,
     .ptr (TailStartC C).stage.cst] r₂.mem r₂.next
  hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
     .ptr (TailStartC C).stage.ctype,
     .ptr (TailStartC C).stage.cst] r₂.mem r₂.next = some r₃

/-- **The document's lane facts at the last entry.**  The root slot's value is not a
field here either: the last entry's openers read it through `HcontOpenCall`'s witness, the
same row the continuing head takes, and the callee's zero at that word is what the refusal
arm answers. -/
structure HlastLane {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The last byte's class, at the high-byte route's two conditions. -/
  tail : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
    evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0 → HlastTailLane G

/-- **The callee rows at the last entry.** -/
structure HlastAbi {m0 : Mem} (G : WalkGeom m0) : Type where
  openCall : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) → HcontOpenCall G C s
  /-- The high-byte class's three calls. -/
  highByte : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
    evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0 → HlastHighByteAbi G C s

/-- **The last entry's payload**: the residual table's rows at the exhausted count,
grouped by kind. -/
structure HlastPayload {m0 : Mem} (G : WalkGeom m0) : Type where
  lane : HlastLane G
  abi : HlastAbi G

/-- **The open bracket's last-entry dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open91_last_of_payload {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hp : HlastPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨rdv, hread, hpreV, r, hcall⟩ := hp.abi.openCall C s hInv hblock hnot
  rcases s2ValuePos_ret_zero_or_one hcall with h1 | h0
  · by_cases hsp : C.sp ≤ 519
    · exact LastEntryArm.dispatch hInv hblock hnot
        (lastEntryArm_containerOpen91_of_staging C s hInv hclass hsp hread hpreV r hcall h1)
    · have h520 : C.sp = 520 := by
        have hcap := hInv.depth_cap
        simp only [stage2StackExtent] at hcap
        omega
      exact LastEntryArm.dispatch hInv hblock hnot
        (lastEntryArm_openAtCap91_of_staging C s hInv hclass h520 hread hpreV r hcall h1)
  · exact LastEntryArm.dispatch hInv hblock hnot
      (lastEntryArm_containerOpenRefuse91_of_staging C s hInv hclass hread hpreV r hcall h0)

/-- **The open brace's last-entry dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open123_last_of_payload {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hp : HlastPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨rdv, hread, hpreV, r, hcall⟩ := hp.abi.openCall C s hInv hblock hnot
  rcases s2ValuePos_ret_zero_or_one hcall with h1 | h0
  · by_cases hsp : C.sp ≤ 519
    · exact LastEntryArm.dispatch hInv hblock hnot
        (lastEntryArm_containerOpen123_of_staging C s hInv hclass hsp hread hpreV r hcall h1)
    · have h520 : C.sp = 520 := by
        have hcap := hInv.depth_cap
        simp only [stage2StackExtent] at hcap
        omega
      exact LastEntryArm.dispatch hInv hblock hnot
        (lastEntryArm_openAtCap123_of_staging C s hInv hclass h520 hread hpreV r hcall h1)
  · exact LastEntryArm.dispatch hInv hblock hnot
      (lastEntryArm_containerOpenRefuse123_of_staging C s hInv hclass hread hpreV r hcall h0)

/-! ### The last entry's high-byte class, from the payload

The class's row is `HlastResidue` — the head's bits, the last byte's class and the three
calls — and this is that structure built from the payload's groups: `lane.tail` supplies
the document's last byte's class and `abi.highByte` the three calls.  The arm then runs
`hlastFacts_of_staging` through `LastEntryArm.dispatch`. -/

/-- **The high-byte class's last-entry arm, from the payload's rows.** -/
def lastEntryArm_highByte_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hnot : ¬ (C.k + 1 < G.nep))
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hp : HlastPayload G) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨hb13, hb32, hbne13⟩ := hp.lane.tail C s hInv hblock hnot hlt125 hne125
  obtain ⟨r₁, r₂, r₃, rdv, xA, hreadT, hpre₁, hcall₁, hret₁, hbit0T, hzread, hpre₂, hcall₂,
    hret₂, hev64, hpre₃, hcall₃⟩ :=
    hp.abi.highByte C s hInv hblock hnot hlt125 hne125
  exact .highByte
    { hlt125 := hlt125
      hne125 := hne125
      hb13 := hb13
      hb32 := hb32
      hbne13 := hbne13
      r₁ := r₁
      r₂ := r₂
      r₃ := r₃
      rdv := rdv
      xA := xA
      hreadT := hreadT
      hpre₁ := hpre₁
      hcall₁ := hcall₁
      hret₁ := hret₁
      hbit0T := hbit0T
      hzread := hzread
      hpre₂ := hpre₂
      hcall₂ := hcall₂
      hret₂ := hret₂
      hev64 := hev64
      hpre₃ := hpre₃
      hcall₃ := hcall₃ }

/-- **The high-byte class's last-entry dispatch, from the payload's rows.** -/
theorem walkDispatch_at_highByte_last_of_payload {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hp : HlastPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_highByte_of_payload hInv hblock hnot hlt125 hne125 hp)

/-! ### The classes the payload reaches, as one dispatch statement

The derivation `JsonStage2WalkDispatchResidual` already proves for the four delimiter bytes,
the payload's openers and the payload's standalone string: those are the classes the
payload covers, and this is their dispatch in one statement, by class selection on the
byte.  The remaining classes are the module header's table. -/

/-- **The continuing classes the payload reaches.**  The four delimiter bytes (their arms
are derived from the invariant by `DerivedHcontClass`), the two container openers (their
root word and call are `lane.root`/`abi.openCall`) and the standalone string at depth zero
(its lane and calls are `lane.string`/`abi.string`). -/
def HcontPayloadClass {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Prop :=
  DerivedHcontClass G C ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1 ∨
  (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1 ∧ C.sp = 0)

/-- **The dispatch at every class the payload covers, from the payload.** -/
theorem walkDispatch_of_payload_covered {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (hp : HcontPayload G)
    (hc : HcontPayloadClass G C) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  rcases hc with hd | h91 | h123 | ⟨h34, hsp0⟩
  · exact walkDispatch_of_derivedClass hInv hblock hk hd
  · exact walkDispatch_at_open91_of_payload hInv hblock hk h91 hp
  · exact walkDispatch_at_open123_of_payload hInv hblock hk h123 hp
  · exact walkDispatch_at_twoEntry_of_payload hInv hblock hk h34 hsp0 hp

/-! ### The payload is inhabited rather than assumed

The continuing payload's rows are all guarded by `C.k + 1 < G.nep`, so at a geometry whose
entry stream is empty every row is the empty function and the predicate is inhabited.  That
is the cheapest witness of consistency this shape admits: the predicate is not
self-contradictory, and the guard it is stated under is the walk's own.

A witness at a *non-empty* document's head would have to supply each row at *every*
invariant head state (`HcontPayload` is a `∀` over states), which is the producer tier the
table above enumerates; it is not a one-document construction, and pretending otherwise
would be the vacuity this module avoids. -/
theorem hcontPayload_of_nep_zero {m0 : Mem} (G : WalkGeom m0) (h : G.nep = 0) :
    Nonempty (HcontPayload G) := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact ⟨fun C s _ _ hk => absurd hk (by omega)⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_entryPos_word
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_rootSlot_word
#print axioms LeanLLVM.Refinement.WalkScope.s2ValuePos_rootWord_of_answer
#print axioms LeanLLVM.Refinement.WalkScope.s2AfterValuePost_rootSlot_at_zero
#print axioms LeanLLVM.Refinement.WalkScope.s2AfterValuePost_rootSlot_above
#print axioms LeanLLVM.Refinement.WalkScope.hlastTail_rootSlot_word
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_logArena_word
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_logCap_word
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_open91_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_open123_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_twoEntry_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_twoEntry_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_of_payload_covered
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_highByte_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_highByte_last_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_open91_last_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_open123_last_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.hcontPayload_of_nep_zero

end WalkScope
end LeanLLVM.Refinement
