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
| `.containerOpen`, `.openAtCap`, `.closeWithOpen`, the four zero refusals, `.commaAboveZero`, `.colonAboveZero` | none — `lane.root` and `abi.open`, and the invariant's own cells | proved below (`…_of_payload`) and in `hcontArm_of_derivedClass` |
| `.twoEntry` | none — `lane.string` and `abi.string` | the class's producer takes exactly these rows plus the invariant; the decoded length and the two log words are the lane's |
| `.ws` | `HcontFacts`'s `hTail` and its `hround`/`hguard`/`hbyte` | the tail starts at a *landing* whose index is the run's stop, and the stop is the run's own count; the scan's traversal rows are `∀`-forms over the latch's recursion, which the payload cannot name before that recursion exists |
| `.cleanup` | the empty tail's three calls | **exposed, and the arm consumes it**: the three links are `emptyTailSeg_of_calls` (`JsonStage2WalkDispatchSegments`) from the value-position, scalar and copy calls' rows, and `hcontArm_cleanup_of_calls` builds the arm at those rows plus the seam's two cells (`contTailStart_ee`, `contTailStart_cond`).  Its head chain is a theorem too: `hcontHeadSeg12_of_cleanup` and `hcontSpan17_of_cleanup` derive the seventeen links from the bundle's fields.  So the payload's `abi` group plus the lane's word produce this class's arm |
| `.scalar` | the empty tail's three calls at the *continuing* route's seam | **the tail's producer is now `scContTail_of_calls`** (`JsonStage2WalkDispatchSegments`): the seam is `scSeamS`, its two test cells are that seam's own peels (`scSeam_ee`, `scSeam_cond`, `JsonStage2WalkHcontScalar`), and `emptyTailSeg_of_calls` composes the three calls at them.  What remains is the arm-level assembly that puts those rows into `HcontScalarFacts` — the bundle's other fields plus the call rows — not a missing cell |
| `.letters`, `.fLetter` | the head's chain to `if.else387.i` | **per head-switch class, and now one theorem per class**: `JsonStage2WalkDispatchLettersHead` factors the chain into the **suffix** every default class shares — `sw.default.i`, the count test's succeeding arm, the bound's `phi`, the whitespace check, the byte's three pivots and the token's end, eight links at *any* state at `sw.default.i` (`contDefaultSeg`) — and the class's **prefix**: `.defaultValueLow`'s three links (`contLowHeadSeg`, eleven in all — the low bytes and every byte above `127`), and `.defaultValueMid`/`.otherValue`/`.defaultValueBracket`/`.defaultValueBracketHigh`'s four (`contMidHeadSeg`, `contOthHeadSeg`, `contBrkHeadSeg`, `contBhHeadSeg`, twelve each).  The arm's field is the class's **count**: `HcontArm.letters`/`.fLetter`/`.classC` take `{nH}` with `hnH : nH ≤ 12` (and the `LastEntryArm` twins `hnH : nH ≤ 11`), which the compositions (`lettersCleanupMerge_at`, `fCleanupMerge_at`, `classCMerge_at`) already took, so the class's chain feeds the constructor at every class.  The chain's *cells* are the payload's now: `HcontLane.defaultLane` carries the next lane's word and read, the bound's compare and the byte before the entry's end with its class, and `JsonStage2WalkDispatchDefaultLane` derives the chain at five of the six head-switch classes (`lowHeadChain_of_lane`, `midHeadChain_of_lane`, `othHeadChain_of_lane`, `brkHeadChain_of_lane`, `bhHeadChain_of_lane`; the sixth, `.defaultValueBrace`/`124`, has its chain `contBrcHeadSeg` and still owes its `_of_lane` producer); what remains for the arm is the tail's three calls and (for `.classC`) the byte's span |
| `.classC` | the byte's own span | **exposed**: `classCSpan_at` produces a span at the arm's endpoint from the class's `slt %8 110` bit alone (the upper bound is not a premise: `126`/`127` take the same leaf), and `classCHeadSpan_at` composes it with the head's twelve at `12 + nS`.  The arm's `hTail` is stated at the span's *endpoint*, which the span returns existentially, so a producer passing both must name the leaf; the span is derivable where the endpoint is named, and is the arm's field otherwise.  Its bytes' head-switch classes are `.defaultValueBracketHigh` (`110 … 122`, `contBhHeadSeg`'s twelve) and `.defaultValueBrace` (`124`, `contBrcHeadSeg`'s twelve: `NodeBlock19 → NodeBlock17 → LeafBlock13 → sw.default.i` then the suffix's eight), so every byte of `[110, 125]` the letters arm does not take has its chain and `.classC`'s `hHead` takes it at `nH ≤ 12`. |
| `.run` | `RunFacts` and its four segments | **composed at the whitespace class, and now at any class's check state**: `HcontRunFacts` is the run's bundle stated at the check state itself — the stop, the landing byte and its seam test, the tail, the landing and the traversal — and `contWsRunF` derives the segment at **any** such state, so the class-C route's `contLandS` is its instance (`hcontRunFacts_of_contFacts`) and no longer its only one.  `JsonStage2WalkDispatchRunHead`'s `wsRunHeadAt`/`wsLandingSegAt` build the head and the landing from the bundle, and `runFacts_of_runBundle` the **whole** `RunFacts`, at `nPre ≤ 8`; `runFacts_of_defaultClass` is the six default classes' producer — the class's prefix to `sw.default.i` plus `contSwToLandSeg`'s four, the bundle, and the class's own span.  At `126`/`127` `runFacts_of_wsFacts` remains the instance, and no `RunFacts` field is a supply there.  What remains is the bundle's *fields* at each class (the payload's document and traversal rows), not a composition |
| the last entry's `.highByte` | none — `HlastLane.tail` and `HlastAbi.highByte` | proved below: the residue `HlastResidue` is *built* from the two groups (`lastEntryArm_highByte_of_payload`), so the bundle is constructed, not assumed |
| the last entry's `.scalar` | the three calls at the scalar route's seam | `JsonStage2WalkDispatchScalarOfStaging` states the producer; its call rows are at the scalar route's own seam state, which the payload's last-level `abi` group does not reach |
| the last entry's `.letters`, `.fLetter`, `.classC`, `.run` | the head's eleven links and the listed spans | `hlastTailSeg` is the last entry's **high-byte** class's sixteen links (six head links, the whitespace check's four, the token's end and the span), not the letters class's; the letters arms at this level take their own chains, whose counts are the continuing ones' minus the count test's `cond.true345.i` (so ten for `.defaultValueLow`, eleven for the four others).  The arm's count is now the class's (`nH` with `nH ≤ 11`), so the shape problem the continuing level had is gone here too; no per-class last-entry chain theorem is stated yet |

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
| the last entry's default arms | a per-class last-entry chain, and the last level's run bundle | the continuing chain's last-entry twin is not stated: the last entry's suffix omits the count test's succeeding arm (`%inc.i ≥ %nep`, so `sw.default.i` leaves for `cond.end349.i` directly), so the letters arms' chains are **ten** links at `.defaultValueLow` and **eleven** at the four others and at `.defaultValueBrace` (one less than the continuing chains' eleven and twelve).  The statement is `contDefaultSeg`'s four-link prefix cut out as `contSwToLandSeg` was, at the *failing* arm and with `%4`'s word for the bound, plus one theorem per prefix class; `hlastTailSeg` is the high-byte class's sixteen links and is not any of them.  `runLastFacts_of_staging` is keyed like the continuing producer, so the last level's run takes `HcontRunFacts` only after this suffix exists |
| `walkContinueFacts_of_payload` | `HcontPayload` → `WalkContinueFacts` | the rows above at every arm; the payload must not hold an arm or a segment, so the class case over `HcontClass.complete` runs each class's producer.  The default arm's chain is in hand; its tail, `.ws`/`.cleanup`'s call rows and `.scalar`'s seam are the rows still listed above |
| `walkLoopEnd_of_payload` | `HlastPayload` → `WalkLoopEnd` | the last entry's rows above, and the terminal log words `WalkLoopEnd.merge`/`.refuse` compose |

A `walkContinueFacts_of_payload` stated over a payload carrying those groups would be a
class case over `HcontClass.complete` with every arm's producer in hand; what this module
will not do is state it over a payload that quietly holds the arms themselves.

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

/-- **The openers' call row**: the precondition at the staged argument list, the outcome
and the contract's `1`. -/
structure HcontOpenCall {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  hpreV : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next
  r : CallOutcome
  hcall : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
     .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r
  hret : r.ret = .int 32 (BitVec.ofNat 32 1)

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
blocks have already laid down, read at the state the arm is read at. -/
structure HcontLane {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The root slot's word: zero, which is what `.containerOpen` and `.openAtCap` read. -/
  root : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4)
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
the guard, or the same call and `if.end.i`'s taken arm to the copy.  The payload supplies
the root slot's zero word and the call's row; everything else is the invariant's. -/

/-- **The open bracket's continuing dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open91_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hp : HcontPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  by_cases hsp : C.sp ≤ 519
  · exact HcontArm.dispatch hInv hblock hk
      (hcontArm_containerOpen91_of_staging C s hInv hclass hsp
        (hp.lane.root C s hInv hblock hk)
        (hp.abi.openCall C s hInv hblock hk).hpreV
        (hp.abi.openCall C s hInv hblock hk).r
        (hp.abi.openCall C s hInv hblock hk).hcall
        (hp.abi.openCall C s hInv hblock hk).hret)
  · have h520 : C.sp = 520 := by
      have hcap := hInv.depth_cap
      simp only [stage2StackExtent] at hcap
      omega
    exact HcontArm.dispatch hInv hblock hk
      (hcontArm_openAtCap91_of_staging C s hInv hclass h520
        (hp.lane.root C s hInv hblock hk)
        (hp.abi.openCall C s hInv hblock hk).hpreV
        (hp.abi.openCall C s hInv hblock hk).r
        (hp.abi.openCall C s hInv hblock hk).hcall
        (hp.abi.openCall C s hInv hblock hk).hret)

/-- **The open brace's continuing dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open123_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hp : HcontPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  by_cases hsp : C.sp ≤ 519
  · exact HcontArm.dispatch hInv hblock hk
      (hcontArm_containerOpen123_of_staging C s hInv hclass hsp
        (hp.lane.root C s hInv hblock hk)
        (hp.abi.openCall C s hInv hblock hk).hpreV
        (hp.abi.openCall C s hInv hblock hk).r
        (hp.abi.openCall C s hInv hblock hk).hcall
        (hp.abi.openCall C s hInv hblock hk).hret)
  · have h520 : C.sp = 520 := by
      have hcap := hInv.depth_cap
      simp only [stage2StackExtent] at hcap
      omega
    exact HcontArm.dispatch hInv hblock hk
      (hcontArm_openAtCap123_of_staging C s hInv hclass h520
        (hp.lane.root C s hInv hblock hk)
        (hp.abi.openCall C s hInv hblock hk).hpreV
        (hp.abi.openCall C s hInv hblock hk).r
        (hp.abi.openCall C s hInv hblock hk).hcall
        (hp.abi.openCall C s hInv hblock hk).hret)

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
    (hstringFacts_of_staging G C s hInv hk heq34 hreadLane hq hreadRoot hsp0 hpreV hxv
      hbranch hcur hreadA hreadC hpreS hwin hy houtn)
    ⟨⟩ hR8

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

/-- **The document's lane facts at the last entry.** -/
structure HlastLane {m0 : Mem} (G : WalkGeom m0) : Type where
  root : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) → readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4)
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
  by_cases hsp : C.sp ≤ 519
  · exact LastEntryArm.dispatch hInv hblock hnot
      (lastEntryArm_containerOpen91_of_staging C s hInv hclass hsp
        (hp.lane.root C s hInv hblock hnot)
        (hp.abi.openCall C s hInv hblock hnot).hpreV
        (hp.abi.openCall C s hInv hblock hnot).r
        (hp.abi.openCall C s hInv hblock hnot).hcall
        (hp.abi.openCall C s hInv hblock hnot).hret)
  · have h520 : C.sp = 520 := by
      have hcap := hInv.depth_cap
      simp only [stage2StackExtent] at hcap
      omega
    exact LastEntryArm.dispatch hInv hblock hnot
      (lastEntryArm_openAtCap91_of_staging C s hInv hclass h520
        (hp.lane.root C s hInv hblock hnot)
        (hp.abi.openCall C s hInv hblock hnot).hpreV
        (hp.abi.openCall C s hInv hblock hnot).r
        (hp.abi.openCall C s hInv hblock hnot).hcall
        (hp.abi.openCall C s hInv hblock hnot).hret)

/-- **The open brace's last-entry dispatch, from the payload's rows.** -/
theorem walkDispatch_at_open123_last_of_payload {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hp : HlastPayload G) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  by_cases hsp : C.sp ≤ 519
  · exact LastEntryArm.dispatch hInv hblock hnot
      (lastEntryArm_containerOpen123_of_staging C s hInv hclass hsp
        (hp.lane.root C s hInv hblock hnot)
        (hp.abi.openCall C s hInv hblock hnot).hpreV
        (hp.abi.openCall C s hInv hblock hnot).r
        (hp.abi.openCall C s hInv hblock hnot).hcall
        (hp.abi.openCall C s hInv hblock hnot).hret)
  · have h520 : C.sp = 520 := by
      have hcap := hInv.depth_cap
      simp only [stage2StackExtent] at hcap
      omega
    exact LastEntryArm.dispatch hInv hblock hnot
      (lastEntryArm_openAtCap123_of_staging C s hInv hclass h520
        (hp.lane.root C s hInv hblock hnot)
        (hp.abi.openCall C s hInv hblock hnot).hpreV
        (hp.abi.openCall C s hInv hblock hnot).r
        (hp.abi.openCall C s hInv hblock hnot).hcall
        (hp.abi.openCall C s hInv hblock hnot).hret)

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
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact fun C s _ _ hk => absurd hk (by omega)
  · exact ⟨fun C s _ _ hk => absurd hk (by omega)⟩

/-! ### The instrument -/

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
