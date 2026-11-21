/-
# The terminal price, as the document has it — and the residual premises, per arm

## 1. The terminal price

`RunLastFacts` (`JsonStage2WalkDispatchRun`) is the last entry's run class, and its
composition `runLastMerge_at` prices the path in the potential the loop's induction
spends: `p + 2 ≤ 32·(G.nep - C.k) + 8·(boundary G G.nep - boundary G C.k)`, which at
`C.k < G.nep` is `walkPotential G C` exactly (`boundary_nep`, `boundary_eq_entryPos`).
The byte term is the document's length read at the exhausted index — `boundary G G.nep =
G.n` — so the credit the entry has left to reach pays the whitespace run and the trailing
scan, and `terminalCharge_boundary` (`JsonStage2WalkTraverse`) reads the same price as the
potential's spend: `(p + 2) + walkPotential (C with k := G.nep) ≤ walkPotential C`.

The entry-only form this module once measured is **retired as a restriction on admitted
inputs**.  `RunLastFacts` used to carry `N + 4 * (c - 1 - i) ≤ 6` — the entry allowance's
remaining six after the path's fixed twenty-four links and the price's own two — and a
terminal run or trailing scan longer than that had no arm, because `entryPos` totalises to
zero at `G.nep` (`entryPos_eq_zero_of_nep_le`) and a byte term read through it charges
nothing.  The bundle's budget fields are now the document's own bounds (the run's count,
its start, the scan's bound) and `runLast_price_with_credit` turns them into the price,
so no document length is restricted; the entry-only form survives as the corollary
`terminalPriceFits_credit`.

This module states the price at the object it is really about: the document's bytes.

* **the class is computable from the document.**  `wsScanStop` finds the whitespace run's
  stop in the byte list; its prefix is `wsCont` and its end is `wsStop`
  (`wsScanStop_class`).  So the run class's per-index conjunct and its stop are a
  *function* of `G.bs`, not an irreducible supply.
* **the price is inside the credit, at every index.**  `terminalPrice_le_credit` is the
  bound with no hypothesis at all: the run's count and the scan's visits fit
  `6 + 8 * (n - ix)`.  `terminalPriceFits` is the entry-only form and
  `terminalPriceFitsCredit` the credit's; `terminalPrice_eight_outside` and
  `terminalPrice_four` are documents on the far side of the six — `"abcdefgh "` and
  `"a   "` — and `terminalPrice_whitespace_twelve` is a long run *and* a long trailing
  scan, all of them inside the credit.
* **the composition's arithmetic.**  `runLast_price_with_credit` is the terminal
  composition's own spending: the fixed twenty-four links, the price's two, the run and
  the scan fit `32 + 8 * (n - ix)` from the run's two document bounds.  `runLastMerge_at`
  applies it, the dispatch states its conclusion at the credit boundary
  (`WalkDispatchResult.mergeLast`, `WalkDispatchOutcome.finish`), and
  `terminalCharge_boundary` reads it as the potential's spend.
* **the trace of the old restriction.**  `runLastFacts_budget_iff_price` is the entry-only
  form's identity at the document's numbers, and `terminalPrice_no_runLastFacts` holds of
  the *arithmetic*: an eight-link terminal run is not `≤ 6` there.  Neither is a statement
  about the bundle any more, because the bundle no longer states that row.

## 2. The residual premises, measured per arm

**The producers are these.**  `hcontFacts_of_staging` (`JsonStage2WalkHcontFactsOfStaging`)
produces `HcontFacts`, the superseded whitespace bundle (its arm was retired with the
route, and no live dispatch builds it); `hlastFacts_of_staging`
(`JsonStage2WalkDispatchWitnessHlast`) produces `HlastFacts` for `LastEntryArm.highByte`;
`JsonStage2WalkDispatchAboveZeroOfStaging` produces the two above-depth classes at both
levels — `hcontArm_commaAboveZero_of_staging`, and `hcontArm_colonAboveZero_of_staging`
beside `lastEntryArm_colonAboveZero_of_staging`; four in
`JsonStage2WalkDispatchZeroOfStaging` fill `HcontArm.commaZero`/`.colonZero` and
`LastEntryArm.commaZero`/`.colonZero`; three in
`JsonStage2WalkDispatchRefusalsOfStaging` fill the bare opener at the last entry
(`lastEntryArm_stringOpener_of_staging`) and the closing bracket at depth zero at both
levels (`hcontArm_closeBracketZero_of_staging`,
`lastEntryArm_closeBracketZero_of_staging`); four in
`JsonStage2WalkDispatchOpenersOfStaging` fill `HcontArm.containerOpen` and
`LastEntryArm.containerOpen`, one producer per byte (`91`, `123`); four in
`JsonStage2WalkDispatchClosersOfStaging` fill `HcontArm.closeWithOpen` and
`LastEntryArm.closeWithOpen`, one per byte (`93`, `125`); and seven in
`JsonStage2WalkDispatchSpansOfStaging` fill the default arm's spans at both levels —
`.letters`, `.fLetter` and `.classC` — beside the last entry's comma
(`lastEntryArm_commaAboveZero_of_staging`, at the end of
`JsonStage2WalkDispatchAboveZeroOfStaging`).  **This round adds four of the six that were
left**
— the scan-free high-byte class (`hcontCleanupFacts_of_staging` and its arm
`hcontArm_cleanup_of_staging`, `JsonStage2WalkDispatchCleanupOfStaging`), the plain-value
class at both levels (`hcontScalarFacts_of_staging`/`hcontArm_scalar_of_staging` and
`lastEntryArm_scalar_of_staging`, `JsonStage2WalkDispatchScalarOfStaging`), and the
standalone string (`hstringFacts_of_staging`/`hcontArm_twoEntry_of_staging`,
`JsonStage2WalkDispatchStringOfStaging`).  **This change adds the tier's last two** — the
run continuation at both levels (`runFacts_of_staging`/`hcontArm_run_of_staging` and
`runLastFacts_of_staging`/`lastEntryArm_run_of_staging`,
`JsonStage2WalkDispatchRunOfStaging`).  **Thirty-eight producers cover twenty-nine arms and
no arm is without one**, each at every state that carries `WalkInv`; beyond its class's byte
test, each takes only its own arm's residual — the depth split, the `519` boundary and the
root word, the entry lane and its order, the byte class of the byte the whitespace check
reads, the level's count, the log words' values and the decoded length, the callee's
staging, and, for the default arm's spans, the head's counted chain and the tail's staging,
which are the class's own.

The run arm's residual is the input's, and it is the largest left: the scan's traversal
(`hbyte`), the head's counted chain to the seam with the run's count inside it, the byte's
span, the tail's three calls on their scan arm, the landing, the scan's counter and its
bound's cell with the copy test's value, and — the one row stated at a document number
rather than at a cell — the lane's order at the continuing entry and the price at the last.
Everything the walk's own blocks bind is derived there: the head byte and its cell, the head
chain's endpoint cell, the landing's two registers, the bound's width, and the price's
document bounds (see the two `run` rows below).

Kind labels: **(i)** per-document class data; **(ii)** callee preconditions/answers;
**(iii)** the scan traversal's round/guard/byte facts.  For (i) the decision is
**D** — a function of the class's byte, `WalkInv`'s registers and the geometry, so a
producer derives it from `HcontClass x`/`HeadArm x` plus `WalkInv` — or **F** — genuinely
free data that only the document or the state supplies.  The definition a **D** item
unfolds is named.  Shared `D` items, named once:

| item | unfolds | source |
|---|---|---|
| head byte, its class bits | `hlastByte G C` = `wsX G (entryPos G C.k)`; `HeadArm`/`HcontClass` | `WalkInv.iter.reg8`, `WalkGeom.doc` |
| `%inc.i`, `%nep`, `%4` | `walkStaticRegs`, `WalkInv.inc_reg` | `WalkInv.regs` |
| `%idxprom.i`, `%5`, `%e`, `%z`, `%s`, `%c.i`, `%t352.i`, `%gap.i` | `walkStaticRegs`, `WalkInv.idx_reg`, `WalkPtrs` | `WalkInv.regs`/`ptrs` |
| the depth (`C.sp`), its zero/positive split, the push guard `C.sp ≤ 519` | `WalkInv.depth_cap` gives `≤ 520` only | **F-split** (see `.containerOpen`) |
| the log's base/arena/capacity words | `WalkInv.log_base`, `log_alen`'s witness, `log_acap` | `WalkInv` (value of `log_alen`'s witness is **F**) |
| the root-done word's *value* | `WalkInv.root_slot` is presence only | **F** |
| the token record's register (`%t352.i`) | `walkStaticRegs` | **D** — `WalkInv.regs`; retired from `RunFacts` and `RunLastFacts` this round (`runScanMerge_at`, `runLastMerge_at` now read the invariant's cell, and the field is gone) |
| the entry stream's next lane (`v`, `entryPos G (C.k+1)`) | `WalkGeom.entries`, `entryPos` | **F** (the input's positions) |
| the byte before the entry's end and its class | `G.bs.getD … 0`, `wsXP`/`wsStopP` | read **D** (frame over the path's writes), value **F** |

### `HcontArm` — 15 constructors

| arm | (i) per-document class data | (ii) calls | (iii) traversal |
|---|---|---|---|
| `ws` (producer `hcontFacts_of_staging`) | **F** `hlt125`/`hne125` (the document's head byte; `HcontClass.defaultValueHigh`); **D** `h8c` and the other six bits given it; **D** the landing reads/`hlatch` given `k`; **F** `v`/`hread`, `hugt`, `hspan`; **D** the class *predicate* and its stop `k` (`wsScanStop`), **F** `C.inner`'s budget conjunct | `r₁ r₂ r₃`, `hTail` | **D** `hround`, the byte's address/read/`%47` cell and the three local facts (`scanRoundField`/`scanByteField`, `JsonStage2WalkRevolutionScanRound`), and the token register (`scanTokField`); **F** one document row, `hbyteClass` — the visited byte's two class bits at `wsByte G (p + 1)`, stated at the visits' span (`k < p + 1`, so `k + 1 … v - 1`), not over every index below the bound: the wide form contradicts the class field's non-whitespace prefix (`cont_hbyteClass_not_wsCont`). The old `hguard` column is gone: `ScanGuard` is false at any state whose registers hold words, and neither traversal lemma reads it (`walkScanRounds457_of_cell`/`walkScanArrival457_of_cell` are guard-free) |
| `cleanup` (producer `hcontCleanupFacts_of_staging`/`hcontArm_cleanup_of_staging`) | **F** `hlt125`/`hne125` (the document's head byte, `HcontClass.defaultValueHigh`); **D** `h8` and `hlt91`/`hlt123`/`b8`/`hend`/`h8end`/`hbit`/`x1`/`h8c`/`hc110`/`hc116`/`hceq116` from it and the cells; **D** counts, `%5`/`%idxprom.i`/`%t352.i`/`%gap.i`; **F** `v`/`hread`, `hspan`, `hugt`; **D** `b35`/`hread35` (the document's byte across the token stores); **F** `hb` (the byte's route) from `b35` | `r₁ r₂ r₃ ev cA rdv xA hTail` | — |
| `twoEntry` (producer `hstringFacts_of_staging`/`hcontArm_twoEntry_of_staging`) | **F** `%8 = 34` (the document's head byte); **D** `h8`/`hlt91`/`hlt44` from it; **D** counts, `%5`/`%4`/`%root_done.i`/widths, `h7`, `hnl`/`hnc`; **F** the next lane `bs`/`hreadLane`/`q`, the root word `rd`, the log words `A`/`Cc`'s values; **D** `hCc` from the capacity read and `log_acap`; **F-split** `hsp0 : C.sp = 0`; **F** `hcur` (`pending = none` is not carried); **D** `HstringResidue` (it is a field-less `Prop`) | `hpreV`/`xv`/`hbranch`, the `s2_string_body` pre/answer | — |
| `scalar` (producer `hcontScalarFacts_of_staging`/`hcontArm_scalar_of_staging`) | **F** the class's three bits (`h44`/`h58`/`hne44`) and the tag test `hbit` at the document's byte (`HcontClass.value`); **D** `h8` and `hlt91` from them; **D** counts, `%5`/`%idxprom.i`/`%t352.i`/`%gap.i`; **F** `v`/`hread`, `hspan`, `hugt`; **D** `b35`/`hread35` (the document's byte across the token stores); **F** `hb` (the byte's route) from `b35` | `r₁ r₂ r₃ ev cA rdv xA hTail` | — |
| `closeBracketZero` | **D** `h8` = 93 (`HeadArm.closeBracket`); **D** `hv`/`he`/`hj`/`hj64`; **F-split** `C.sp = 0` | — | — |
| `commaZero` | **D** `h8` = 44; **D** the rest; **F-split** `C.sp = 0` | — | — |
| `colonZero` | **D** `h8` = 58; **D** the rest; **F-split** `C.sp = 0` | — | — |
| `commaAboveZero` | **D** `h8` = 44; **D** `hmark`/`hstate` (witnesses `C.tyMap (C.sp-1)`, `C.stMap (C.sp-1)`); **F-split** `C.sp ≠ 0` | — | — |
| `colonAboveZero` | **D** `h8` = 58; **D** `hmark`/`hstate`; **F-split** `C.sp ≠ 0` | — | — |
| `containerOpen` | **D** `h8`/`hopen` (91/123); **F-split/boundary** `hsp519`: `depth_cap` gives `C.sp ≤ 520`, and the block's own `ugt %sp.i 519` test takes `if.then21.i` at `C.sp = 520` instead of this route — a depth *selector* the invariant does not settle, and no arm covers that branch here; **F** `hrd` (the root word's zero value) | `hpreV`, `r`, `hcall`, `hret` | — |
| `closeWithOpen` | **D** `h8`/`hv` (93/125); **D** `hmark`/`hstate`, `hvj`/`he`/`hj`/`hj64`; **F-split** `C.sp ≠ 0` | `hpreA` (`s2_after_value`) | — |
| `letters` | **F** the byte (`hlastByte G C` is the document's byte at the entry's position — `WalkInv.iter.reg8` names the cell, not the value); **D** the tests given it (`hbit`/`h110`/`hne102` are functions of that byte) and `h8` once it is named; **D** `hm`/`hmk`/`h8m`/`ht`/`htk`/`htok`; **D** `hHead` (the head's twelve links are class-independent, so a function of the class and the document — currently a field) | `hTail` | — |
| `fLetter` | as `letters`, with its `h102` test **D** given the same byte | `hTail` | — |
| `classC` | **F** the byte; **D** `h110`/`h125` given it, hence `h8`; **D** `hHead`, `hnS`, `htok`; **D** `hSpan` (the byte's own leaf: `c56TrueSpan`, `c56ElseSpan`, `c58TrueSpan`, `c58ElseSpan`) | `hTail` | — |
| `run` (producer `runFacts_of_staging`/`hcontArm_run_of_staging`) | **D** `N` (= `k - ix`, `wsScanStop`); **D, derived by the producer** `x`/`h8` (`WalkInv.iter.reg8`), `h8m` (the head chain's endpoint `WalkIter`, at `hmk` — the row the spans' arms carry as an arm field), `hinc`/`hnep` (the landing's endpoint invariant), `hcw` (`entryPos_lt` at the guard), `hbudget` (the byte allowance's eight per visit implies the field's four — `runBudget_of_bytePrice`, whose premise is `contWsPriceF`'s form carried by `runBudget_of_wsPrice`); **D-in-principle** the segments `hHead`, `hSpan`, `hLatch` and their endpoints (the class's own; no class-independent composition exists, since the pivots take different blocks per byte); **F** `hbit` (the tag test at the document's head byte), `i`/`c` and `hic` (`WalkInv` names neither cell), `hspanStart` (the lane), `hstart` (the run's start) | `hTail` | `hbyte` |

### `LastEntryArm` — 14 constructors

| arm | (i) per-document class data | (ii) calls | (iii) traversal |
|---|---|---|---|
| `scalar` (producer `lastEntryArm_scalar_of_staging`) | **F** the class's three bits (`h44`/`h58`/`hne44`) and the tag test `hbit` at the document's byte (`HeadArm.defaultValue`, tag `1`); **D** `h8` and `h91` from them; **D** `hread35` (the document's last byte across the prefix's token stores) with the byte `G.bs.getD (G.n-1) 0`; **F** `hb13/hb32/hbne32` from it; **F** `hreadT` (the `%root_done` word at `G.next0+8`); **D** `hzread` (`WalkInv.log_base` across the kind store, the token record and the log being separate staged objects), `hev64` (`WalkGeom.evLt`) | `hpre₁`/`hcall₁`/`hret₁`/`hbit0T`, `hpre₂`/`hcall₂`/`hret₂`, `hpre₃`/`hcall₃` | — |
| `highByte` (producer `hlastFacts_of_staging`) | **F** `hlt125`/`hne125` — the document's head byte, and the two bits **are** the class: `HeadArm.defaultValueHigh`, bytes 126/127; **D** `hb13`/`hb32`/`hbne13` given the last byte `G.bs.getD (G.n-1) 0`; **F** `hreadT`; **D** `hzread`, `hev64` | `hpreᵢ`/`hcallᵢ`/`hretᵢ` (three) | — |
| `stringOpener` | **D** `h8` = 34; **D** `hinc`/`hnep`/`hge` (from the consumer's `¬(C.k+1<nep)` and the static cells), `he` (the offset is the entry's position, off `WalkInv.idx_reg`, so the arm carries no operand fact); **F-split** `¬ (C.k + 1 < G.nep)` — the level's own selector, which the constructor does not carry at either level | — | — |
| `closingZero` | **D** `h8` = 93; **D** `hv`/`he`/`hj`/`hj64`; **F-split** `C.sp = 0` | — | — |
| `commaZero` | **D** 44; **D** the rest; **F-split** `C.sp = 0` | — | — |
| `colonZero` | **D** 58; **D** the rest; **F-split** `C.sp = 0` | — | — |
| `commaAboveZero` | **D** 44; **D** `hmark`/`hstate`; **F-split** `C.sp ≠ 0` | — | — |
| `colonAboveZero` | **D** 58; **D** `hmark`/`hstate`; **F-split** `C.sp ≠ 0` | — | — |
| `containerOpen` | **D** 91/123; **F-split/boundary** `hsp519` (as above); **F** `hrd` | `hpreV`, `r`, `hcall`, `hret` | — |
| `closeWithOpen` | **D** 93/125; **D** `hmark`/`hstate`, cells; **F-split** `C.sp ≠ 0` | `hpreA` | — |
| `letters` | **F** the byte; **D** its class bits given it and `h8` once it is named; **D** `hHead` (eleven links, class-independent), endpoint cells, `htok` | `hTail` | — |
| `fLetter` | as `letters`, with its `h102` test **D** given the same byte | `hTail` | — |
| `classC` | **F** the byte; **D** `h110`/`h125` given it, hence `h8`; **D** `hHead`/`hSpan`/`hnS`/`htok` | `hTail` | — |
| `run` (producer `runLastFacts_of_staging`/`lastEntryArm_run_of_staging`) | **F** `hbit` (the tag test at the document's head byte); **D, derived by the producer** `x`/`h8`, `h8m`, `hinc`/`hnep`, `hcw` (`G.maxDoc` at the bound), `hspanDoc` (`hc`, the bound being `%4`, at `le_of_eq`), `hstart` (`terminalStop_ge`) and `hNdoc` (`terminalStop_le` at the document's length) — the three document bounds section 1's price consumes; **D-in-principle** the segments `hHead`/`hSpan`/`hLatch` and their endpoints; **F** `i`/`c` and `hic`, and the document's three numbers | `hTail` | `hbyte` |

**What the enumeration decides.**  The **F** rows are the document's content (the entry
stream's lanes, the bytes the paths read, the root word, the log word's value) and the
walk's free depth; the **D** rows are the head byte's class, the invariant's cells, and
the paths' segments — a function of the class and the geometry.  So the remaining tier is
**not** one general class-demotion lemma: the class bits, the segments and the registers
demote generically, but the **F** rows need per-class producers (the lane word, the
byte's class, the stop, the root word, the depth split), and the **(ii)/(iii)** rows need
the callee contracts at their own memories and the traversal lemmas before any class can
be produced at an arbitrary document.

## 3. The closure claim, as it now reads

**The obligation's two bundles are still supplied**, with these named obstructions:

* `WalkContinueFacts` — 15 arms, all with a producer (`.ws` through
  `hcontFacts_of_staging`, the depth-zero refusals, the above-depth comma and colon, the
  openers, the closing delimiters, the default arm's three spans in
  `JsonStage2WalkDispatchSpansOfStaging`, and this round's scan-free high-byte class
  (`hcontCleanupFacts_of_staging`, `JsonStage2WalkDispatchCleanupOfStaging`), plain-value
  class (`hcontScalarFacts_of_staging`, `JsonStage2WalkDispatchScalarOfStaging`),
  standalone string (`hstringFacts_of_staging`,
  `JsonStage2WalkDispatchStringOfStaging`) and run continuation (`runFacts_of_staging`,
  `JsonStage2WalkDispatchRunOfStaging`)), and each keeps its own (ii) calls, its (iii)
  traversal rows where the class has a scan, and the **F** document rows above.  `.run`'s
  residual is the traversal (`hbyte`), the head chain and span, the tail's scan arm, the
  landing, the scan's two cells and the lane's order — none of them a class demotion: the
  refusal, opener and token classes are produced, and the run bundle's every
  invariant-side row is derived, so a class-demotion lemma is not what the residual needs.
* `WalkLoopEnd` — 14 arms plus the two log words.  **`.highByte` carries its producer's
  supply, not its conclusion**: the arm's payload is `HlastResidue` — the head byte's two
  naming bits, the last byte's three class bits, the root word, the three calls' staged
  arguments and answers, and the log's base word — and `LastEntryArm.dispatch` applies
  `hlastFacts_of_staging` to it, so the rows that producer derives (the `%8` cell and the
  other six class bits, the last index and its width, the last byte and its read, the tail's
  segment, the finalisation's registers and the merge's cells) appear nowhere in the arm.
  The residual is therefore *not* "the same (ii) residuals" the continuing arms keep: it is
  that supply, which is more.  `.scalar` has this round's producer
  (`lastEntryArm_scalar_of_staging`), which derives the same rows from the plain-value
  class's bits — including the log's base word, which the high-byte residue still supplies
  and this arm's producer reads off `WalkInv.log_base` across the kind store — so its arm
  keeps the class bits, the last byte's class, the root word and the three calls.
  `hlast`'s other arms are as `WalkContinueFacts`'s, with `.run` now produced by
  `runLastFacts_of_staging`/`lastEntryArm_run_of_staging` — its bundle keeps the segments,
  the tail's calls and the traversal, and derives the price's three document bounds from
  the stop, the length and the run's start (§2's `run` rows); `mergeWords`/`refuseWords`
  are the log word, which is
  **false** at an escaping input (`JsonStage2WalkArenaWord`) and is a statement change, not
  a proof.

Nothing about the walk's statements is retracted by that.  What is retracted is the
brief's claim that **composition alone** would produce the two bundles: with every arm
produced, what stands between here and Gate A is the arms' residuals — the callee contracts
at the tails' argument lists, the traversal hypotheses (`hround`, `hguard`, `hbyte`), the
classes' head chains and spans, and the document rows — not a new composition.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchRun
import LeanLLVM.Refinement.JsonStage2WalkRevolution
import LeanLLVM.Refinement.JsonStage2WalkDispatchBase

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The bytes' class, as a computable predicate -/

/-- The byte's register value, at the byte list rather than the geometry. -/
def wsXP (bs : List UInt8) (q : Nat) : BitVec 8 := BitVec.ofNat 8 (bs.getD q 0).toNat

/-- `wsCont` at the byte list: the byte takes one leaf's back edge. -/
def wsContP (bs : List UInt8) (q : Nat) : Prop :=
  (evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (wsXP bs q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) ∨
    (evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 32) = 1 ∧
      evalICmp .eq (wsXP bs q) (BitVec.ofNat 8 13) = 0) ∨
    (evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 32) = 0 ∧
      evalICmp .eq (wsXP bs q) (BitVec.ofNat 8 32) = 0)

/-- `wsStop` at the byte list: the byte leaves its leaf for `if.end372.i`. -/
def wsStopP (bs : List UInt8) (q : Nat) : Prop :=
  (evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (wsXP bs q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
    (evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 32) = 1 ∧
      evalICmp .eq (wsXP bs q) (BitVec.ofNat 8 13) = 1) ∨
    (evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 32) = 0 ∧
      evalICmp .eq (wsXP bs q) (BitVec.ofNat 8 32) = 1)

/-- The stop test is a decision: its atoms are bit tests. -/
instance wsStopP_decidable (bs : List UInt8) (q : Nat) : Decidable (wsStopP bs q) := by
  unfold wsStopP wsXP
  infer_instance

/-- The list's byte is the geometry's: `wsX` reads `G.bs` and nothing else. -/
theorem wsXP_eq {m0 : Mem} (G : WalkGeom m0) (q : Nat) : wsXP G.bs q = wsX G q := by
  simp only [wsXP, wsX, wsByte]

/-- A continuing byte at the list is a continuing byte at the geometry. -/
theorem wsContP_iff {m0 : Mem} (G : WalkGeom m0) (q : Nat) :
    wsContP G.bs q ↔ wsCont G q := by
  simp only [wsContP, wsCont, wsXP, wsX, wsByte]

/-- A stopping byte at the list is a stopping byte at the geometry. -/
theorem wsStopP_iff {m0 : Mem} (G : WalkGeom m0) (q : Nat) :
    wsStopP G.bs q ↔ wsStop G q := by
  simp only [wsStopP, wsStop, wsXP, wsX, wsByte]

/-- **Every byte either continues the run or stops it.**  The three leaves' tests are one
bit each and the complement of the continuing arm is the stopping one, so the disjunction
is exhaustive — this is what makes the class a decision rather than a supply. -/
theorem wsStopP_or_wsContP (bs : List UInt8) (q : Nat) :
    wsStopP bs q ∨ wsContP bs q := by
  unfold wsStopP wsContP
  by_cases h13 : evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 1
  · by_cases h910 : evalICmp .ule (wsXP bs q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
    · exact Or.inl (Or.inl ⟨h13, h910⟩)
    · exact Or.inr (Or.inl ⟨h13, bitZeroOfNeOne h910⟩)
  · have h13' : evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 13) = 0 := bitZeroOfNeOne h13
    by_cases h32 : evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 32) = 1
    · by_cases he13 : evalICmp .eq (wsXP bs q) (BitVec.ofNat 8 13) = 1
      · exact Or.inl (Or.inr (Or.inl ⟨h13', h32, he13⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h13', h32, bitZeroOfNeOne he13⟩))
    · have h32' : evalICmp .slt (wsXP bs q) (BitVec.ofNat 8 32) = 0 := bitZeroOfNeOne h32
      by_cases he32 : evalICmp .eq (wsXP bs q) (BitVec.ofNat 8 32) = 1
      · exact Or.inl (Or.inr (Or.inr ⟨h13', h32', he32⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h13', h32', bitZeroOfNeOne he32⟩))

/-! ### The run's stop, computed

The skip is a scan from the entry's position: it advances while the byte continues and
stops at the first byte that does not.  `wsScanStop` is that scan, at the fuel the
document leaves it, so the stop it returns is the run class's own witness. -/

/-- The skip's stop from `q`, within `fuel` visits: the first stopping byte, or `q + fuel`
when the fuel runs out. -/
def wsScanStop (bs : List UInt8) (q fuel : Nat) : Nat :=
  match fuel with
  | 0 => q
  | n + 1 => if wsStopP bs q then q else wsScanStop bs (q + 1) n

/-- The scan does not go back. -/
theorem wsScanStop_ge (bs : List UInt8) (q fuel : Nat) :
    q ≤ wsScanStop bs q fuel := by
  induction fuel generalizing q with
  | zero => exact le_rfl
  | succ n ih =>
    show q ≤ (if wsStopP bs q then q else wsScanStop bs (q + 1) n)
    by_cases hs : wsStopP bs q
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs]
      exact le_trans (Nat.le_succ q) (ih (q + 1))

/-- The scan stays inside its fuel. -/
theorem wsScanStop_le (bs : List UInt8) (q fuel : Nat) :
    wsScanStop bs q fuel ≤ q + fuel := by
  induction fuel generalizing q with
  | zero => exact le_refl _
  | succ n ih =>
    show (if wsStopP bs q then q else wsScanStop bs (q + 1) n) ≤ q + (n + 1)
    by_cases hs : wsStopP bs q
    · rw [ite_eq_left hs]; omega
    · rw [ite_eq_right hs]
      have := ih (q + 1)
      omega

/-- **Every byte before the stop continues the run.**  The class's `∀ q ∈ [ix, k)`
conjunct, produced by the scan. -/
theorem wsScanStop_cont (bs : List UInt8) {q q' fuel : Nat} (hq : q ≤ q')
    (h : q' < wsScanStop bs q fuel) : wsContP bs q' := by
  induction fuel generalizing q with
  | zero =>
    have h' : q' < q := h
    omega
  | succ n ih =>
    have h' : q' < (if wsStopP bs q then q else wsScanStop bs (q + 1) n) := h
    by_cases hs : wsStopP bs q
    · rw [ite_eq_left hs] at h'
      omega
    · rw [ite_eq_right hs] at h'
      rcases Nat.eq_or_lt_of_le hq with heq | hlt
      · subst heq
        exact (wsStopP_or_wsContP bs q).resolve_left hs
      · exact ih (q := q + 1) (by omega) h'

/-- **The stop is a stopping byte**, when the scan stopped inside its fuel. -/
theorem wsScanStop_stop (bs : List UInt8) {q fuel : Nat}
    (h : wsScanStop bs q fuel < q + fuel) : wsStopP bs (wsScanStop bs q fuel) := by
  induction fuel generalizing q with
  | zero =>
    have h' : q < q + 0 := h
    omega
  | succ n ih =>
    have h' : (if wsStopP bs q then q else wsScanStop bs (q + 1) n) < q + (n + 1) := h
    by_cases hs : wsStopP bs q
    · have he : wsScanStop bs q (n + 1) = q := by
        show (if wsStopP bs q then q else wsScanStop bs (q + 1) n) = q
        rw [ite_eq_left hs]
      rw [he]
      exact hs
    · rw [ite_eq_right hs] at h'
      have he : wsScanStop bs q (n + 1) = wsScanStop bs (q + 1) n := by
        show (if wsStopP bs q then q else wsScanStop bs (q + 1) n) =
          wsScanStop bs (q + 1) n
        rw [ite_eq_right hs]
      rw [he]
      exact ih (q := q + 1) (by omega)

/-- **The run class, at the geometry**: the scan's prefix continues and its end stops.
`hcont` is the class's per-index conjunct and `hstop` its stop, produced rather than
supplied. -/
theorem wsScanStop_class {m0 : Mem} (G : WalkGeom m0) {q fuel : Nat}
    (h : wsScanStop G.bs q fuel < q + fuel) :
    (∀ q', q ≤ q' → q' < wsScanStop G.bs q fuel → wsCont G q') ∧
      wsStop G (wsScanStop G.bs q fuel) :=
  ⟨fun q' hq hq' => (wsContP_iff G q').1 (wsScanStop_cont G.bs hq hq'),
   (wsStopP_iff G _).1 (wsScanStop_stop G.bs h)⟩

/-! ### The terminal price, at the document

At the last entry the entry's end is the document's length, so the run starts at the
entry's position `ix` and stops at `wsScanStop`'s answer `k`, and the extra-token scan
visits `[k, n)`.  The price is the run's count plus four per visited byte. -/

/-- The terminal run's stop at the document's own fuel. -/
def terminalStop (bs : List UInt8) (ix : Nat) : Nat := wsScanStop bs ix (bs.length - ix)

/-- **The terminal price**: the run's count plus the scan's visits at four links each. -/
def terminalPrice (bs : List UInt8) (ix : Nat) : Nat :=
  (terminalStop bs ix - ix) + 4 * (bs.length - 1 - terminalStop bs ix)

/-- **The entry allowance's form**: the terminal price inside the six links the entry
allowance leaves after the path's fixed twenty-four and its own two.  It is a computable
predicate of the document (`terminalPrice_eight_outside`, `terminalPrice_two`), and it is
not the bundle's budget any more: `terminalPriceFits_credit` is the implication that
survives, and the budget's rows are the document's own bounds. -/
def terminalPriceFits (bs : List UInt8) (ix : Nat) : Prop := terminalPrice bs ix ≤ 6

/-- **The credit's form**: the entry allowance plus the document bytes the walk has left
to reach, which is what `boundary`'s byte term pays at the terminal index. -/
def terminalPriceFitsCredit (bs : List UInt8) (ix : Nat) : Prop :=
  terminalPrice bs ix ≤ 6 + stage2ByteAllowance * (bs.length - ix)

instance terminalPriceFits_decidable (bs : List UInt8) (ix : Nat) :
    Decidable (terminalPriceFits bs ix) := by
  unfold terminalPriceFits terminalPrice
  infer_instance

instance terminalPriceFitsCredit_decidable (bs : List UInt8) (ix : Nat) :
    Decidable (terminalPriceFitsCredit bs ix) := by
  unfold terminalPriceFitsCredit terminalPrice
  infer_instance

theorem terminalStop_ge (bs : List UInt8) (ix : Nat) : ix ≤ terminalStop bs ix :=
  wsScanStop_ge bs ix (bs.length - ix)

theorem terminalStop_le (bs : List UInt8) {ix : Nat} (hix : ix ≤ bs.length) :
    terminalStop bs ix ≤ bs.length := by
  have := wsScanStop_le bs ix (bs.length - ix)
  simp only [terminalStop]
  omega

/-! ### The two prices, and the difference -/

/-- **The price is inside the credit, at every index.**  No hypothesis on the document or
the index: the stop is at or after the entry's position and — when the scan had the fuel
to reach it — at most the document's end, and when the index is already past the document
the run and the scan are both empty.  So the run's count and the scan's four-per-visit
visits fit `6 + 8 * (n - ix)`: the six the entry allowance leaves and eight per document
byte from the entry's position to the document's end. -/
theorem terminalPrice_le_credit (bs : List UInt8) (ix : Nat) :
    terminalPrice bs ix ≤ 6 + stage2ByteAllowance * (bs.length - ix) := by
  by_cases hix : ix ≤ bs.length
  · have hge := terminalStop_ge bs ix
    have hle := terminalStop_le bs hix
    have h1 : terminalStop bs ix - ix ≤ bs.length - ix := by omega
    have h2 : bs.length - 1 - terminalStop bs ix ≤ bs.length - ix := by omega
    simp only [terminalPrice, stage2ByteAllowance]
    omega
  · have hz : bs.length - ix = 0 := by omega
    have hs : terminalStop bs ix = ix := by
      show wsScanStop bs ix (bs.length - ix) = ix
      rw [hz]
      rfl
    have hz' : bs.length - 1 - ix = 0 := by omega
    simp only [terminalPrice, stage2ByteAllowance, hs, hz, hz']
    omega

/-- **The entry-only form implies the credit's.**  The short-path result, as the corollary
it is: `6` is inside `6 + 8 * (n - ix)`, so every price the old form paid, the credit pays.
What the implication does *not* say is that the entry-only form holds — a terminal run of
more than six links is inside the credit and outside the six. -/
theorem terminalPriceFits_credit {bs : List UInt8} {ix : Nat}
    (h : terminalPriceFits bs ix) : terminalPriceFitsCredit bs ix := by
  have := terminalPrice_le_credit bs ix
  simp only [terminalPriceFitsCredit, terminalPriceFits] at h ⊢
  omega

/-- **At the document's end the two forms coincide**: with no byte left to reach the
credit is the entry's six. -/
theorem terminalPrice_entryOnly_of_credit (bs : List UInt8) (ix : Nat)
    (h : terminalPriceFitsCredit bs ix) (hn : bs.length ≤ ix) : terminalPriceFits bs ix := by
  have hz : bs.length - ix = 0 := by omega
  simp only [terminalPriceFitsCredit, terminalPriceFits, stage2ByteAllowance, hz,
    Nat.mul_zero, Nat.add_zero] at h ⊢
  exact h

/-! ### The documents on either side

`"abcdefgh "` is eight continuing bytes and a trailing space: the run is eight, the scan
is empty, and the entry-only price is eight — outside the six, so the entry allowance did
not pay for it.  `"a "` is one continuing byte and a
space: the price is one.  `"a   "` stops after the first byte and scans three. -/

/-- Eight continuing bytes then a space: the terminal run is eight links. -/
theorem terminalPrice_eight :
    terminalStop [97, 98, 99, 100, 101, 102, 103, 104, 32] 0 = 8 ∧
      terminalPrice [97, 98, 99, 100, 101, 102, 103, 104, 32] 0 = 8 := by
  decide

/-- **A document outside the entry-only price, and inside the credit.**  This is the
boundary's non-emptiness at an ordinary input, and the credit form paying for it. -/
theorem terminalPrice_eight_outside :
    ¬ terminalPriceFits [97, 98, 99, 100, 101, 102, 103, 104, 32] 0 ∧
      terminalPriceFitsCredit [97, 98, 99, 100, 101, 102, 103, 104, 32] 0 := by
  decide

/-- `"a "`: one continuing byte, then the stop.  The price is one, so the entry-only form
pays for the `"a "` regression's class (`JsonStage2WalkDispatchRunLastDomain`). -/
theorem terminalPrice_two : terminalPriceFits [97, 32] 0 := by decide

/-- `"a   "`: one continuing byte and three spaces.  The run stops after the first byte
and the scan visits two, so the entry-only price is nine and the credit pays it. -/
theorem terminalPrice_four :
    terminalPrice [97, 32, 32, 32] 0 = 9 ∧
      ¬ terminalPriceFits [97, 32, 32, 32] 0 ∧
      terminalPriceFitsCredit [97, 32, 32, 32] 0 := by
  decide

/-- **A document with both a long run and a long trailing scan.**  Eight letters then four
spaces: the run is eight links, the scan visits three more, and the price is `8 + 12 = 20`
— three times the six the entry allowance leaves, so the entry-only form excludes it
(`¬ terminalPriceFits`).  The credit pays it, and so does the composition's own
arithmetic: the fixed twenty-four links and the price's two beside the twenty are
`46 ≤ 32 + 96`, the entry allowance plus eight per byte of the twelve.
This is the shape the old restriction had no arm for. -/
theorem terminalPrice_whitespace_twelve :
    terminalPrice [97, 98, 99, 100, 101, 102, 103, 104, 32, 32, 32, 32] 0 = 20 ∧
      ¬ terminalPriceFits [97, 98, 99, 100, 101, 102, 103, 104, 32, 32, 32, 32] 0 ∧
      terminalPriceFitsCredit [97, 98, 99, 100, 101, 102, 103, 104, 32, 32, 32, 32] 0 ∧
      terminalPrice [97, 98, 99, 100, 101, 102, 103, 104, 32, 32, 32, 32] 0 + 26 ≤
        stage2EntryAllowance + stage2ByteAllowance * 12 := by
  decide

/-- **The composition prices that document.**  The same twelve bytes at the terminal
index, with the numbers a producer of the run class supplies: the stop is `8`, so the
run's count is `8` and the scan's three visits are `12` links; the head chain is
`11 + 8 ≤ 19` and the byte's span at most `5`; the entry is at `0` and the document is
`12`.  `runLast_price_with_credit` — the lemma `runLastMerge_at` applies to a
`RunLastFacts`'s three document bounds — then pays the whole `46`-link path out of the
entry allowance and the ninety-six byte links, `46 ≤ 128`.  Under the entry-only form the
same numbers are `46 ≤ 32 + 0`: there was no arm, and there is no premise here that could
hold only for a short document. -/
theorem runLast_price_whitespace_twelve :
    (11 + 8) + 5 + 8 + 12 + 2 ≤ stage2EntryAllowance + stage2ByteAllowance * 12 :=
  runLast_price_with_credit (nH := 19) (nS := 5) (nSc := 12) (N := 8) (c := 12) (i := 8)
    (ix := 0) (n := 12) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ### The bridge to the bundle's field -/

/-- **The entry-only form is the legacy arithmetic, at the document's own numbers.**  The
three equalities are the producer's: `WalkInv` names neither the scan's counter nor its
bound, so a producer of the run class supplies them (with `hix`, the run starting at the
entry's position).  This is the *retired* row's arithmetic — `RunLastFacts` now carries the
document's bounds and the composition applies `runLast_price_with_credit` — and
`JsonStage2WalkDispatchResidual` reads it as the measurement of a document against the
form the bundle no longer states. -/
theorem runLastFacts_budget_iff_price {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (f : RunLastFacts G C s)
    (_hix : entryPos G C.k ≤ f.i)
    (hk : f.i = terminalStop G.bs (entryPos G C.k))
    (hc : f.c = G.n) (hN : f.N = f.i - entryPos G C.k) :
    terminalPriceFits G.bs (entryPos G C.k) ↔
      f.N + 4 * (f.c - 1 - f.i) ≤ 6 := by
  have hbs : G.bs.length = G.n := walkReadBytes_length G.doc
  simp only [terminalPriceFits, terminalPrice]
  rw [hbs, ← hk, ← hc, ← hN]

/-- **The entry-only row is false at the document's numbers, for a long run.**  The *row*,
not the bundle: `RunLastFacts` no longer states it.  The walk accepts such a document (it
is fuel-bounded) and the composition prices it out of the document's credit
(`runLast_price_with_credit`); what remains true is the arithmetic — an eight-link
terminal run is not `≤ 6` at the stop, the length and the run's start. -/
theorem terminalPrice_no_runLastFacts {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {f : RunLastFacts G C s}
    (hix : entryPos G C.k ≤ f.i)
    (hk : f.i = terminalStop G.bs (entryPos G C.k))
    (hc : f.c = G.n) (hN : f.N = f.i - entryPos G C.k)
    (hout : ¬ terminalPriceFits G.bs (entryPos G C.k)) :
    ¬ (f.N + 4 * (f.c - 1 - f.i) ≤ 6) :=
  fun hbudget => hout ((runLastFacts_budget_iff_price f hix hk hc hN).2 hbudget)

/-! ### The credit's arithmetic

The terminal price is stated at the potential the induction spends.  `mergeLast`
(`JsonStage2WalkDispatchThreeOfRun`) states it at `k2 = G.nep` with the byte term read at
the credit boundary: `boundary G G.nep = G.n` (`boundary_nep`, `JsonStage2WalkTraverse`),
so the last entry's remaining byte allowance is `8 * (G.n - entryPos G C.k)` and the
price's right-hand side is `walkPotential G C` at `C.k < G.nep`.

`runLast_price_with_credit` is that arithmetic, and `runLastMerge_at`
(`JsonStage2WalkDispatchRun`) applies it: the three document bounds are the bundle's
fields, and the fixed part is the terminal path's own twenty-four links.  Nothing here
names the entry allowance's six, and nothing restricts the document's length. -/

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.wsStopP_or_wsContP
#print axioms LeanLLVM.Refinement.WalkScope.wsScanStop_cont
#print axioms LeanLLVM.Refinement.WalkScope.wsScanStop_stop
#print axioms LeanLLVM.Refinement.WalkScope.wsScanStop_class
#print axioms LeanLLVM.Refinement.WalkScope.terminalPrice_le_credit
#print axioms LeanLLVM.Refinement.WalkScope.terminalPriceFits_credit
#print axioms LeanLLVM.Refinement.WalkScope.terminalPrice_eight_outside
#print axioms LeanLLVM.Refinement.WalkScope.terminalPrice_four
#print axioms LeanLLVM.Refinement.WalkScope.terminalPrice_whitespace_twelve
#print axioms LeanLLVM.Refinement.WalkScope.runLast_price_whitespace_twelve
#print axioms LeanLLVM.Refinement.WalkScope.runLastFacts_budget_iff_price
#print axioms LeanLLVM.Refinement.WalkScope.terminalPrice_no_runLastFacts

end WalkScope
end LeanLLVM.Refinement
