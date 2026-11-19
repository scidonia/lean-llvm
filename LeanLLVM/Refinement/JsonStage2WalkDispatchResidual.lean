/-
# The dispatch's residual rows, and the classes that need none

`WalkContinueFacts` (`JsonStage2WalkDispatchHcontArms`) and `WalkLoopEnd`
(`JsonStage2WalkPremisesOfStaging`) are the loop's two bundles: the continuing entry's arm
at every invariant head with an entry left, and the last entry's arm at every invariant
head without one.  Both are produced from payload rows — `walkContinueFacts_of_payload`
and `walkLoopEnd_of_payload` — and this module states, per class, which rows the arms
need, and produces the part the invariant alone supplies:

* at the classes whose rows the layer **derives**, the arm is a theorem at every state
  that carries the invariant — `hcontArm_of_derivedClass` and
  `lastEntryArm_of_derivedClass`, through `HcontArm.dispatch` and `LastEntryArm.dispatch`;
* at the remaining classes the arm's payload is a row that no clause of `WalkInv` supplies,
  and the table below names which row, and from which producer;
* the terminal price row is derived, not supplied: at the document `"abcdefgh "` the
  entry allowance's form of it is false (`entryOnlyBudget_false_at_eight`), and the price
  is read at the credit boundary instead — `JsonStage2WalkTerminalPrice`'s credit form at
  the document's own bounds, which `runLastMerge_at` applies.

## The classes whose rows are all derived

`DerivedHcontClass` is the comma and the colon at either depth, the closing bracket at
either depth, and the closing brace at either depth; `DerivedLastClass` adds the bare
string opener, which at a continuing head is the two-entry string's class instead.  Each
arm's producer takes the class's byte test and, where the arm reads it, the depth's split,
and derives every cell: the `%8` word (`cont_reg8`, `WalkInv.iter.reg8`), the entry's
position (`WalkInv.idx_reg`), `%e` and the two document bounds (`WalkInv.regs`,
`entryPos_le`, `entryPos_lt_64`), the two stack bytes (the carry's maps at `%sp - 1`, read
by `rfl`), the count test's clear bit (`quoteCount_ge`), and — this is what
`s2AfterValuePre_of_inv` adds — the closing delimiters' callee precondition: the top stack
byte at `%ctype.i + (%sp - 1) - 1` exists because the mark covers the depth
(`WalkInv.sp_le_wlen`, `WalkInv.tyBytes`) and `%sp - 1` is the emitted subtraction
(`pairOff_eq`).  So the `s2_after_value` call at those arms is a *contract*, not a supply:
`s2AfterValue_answers` (`JsonStage2Helpers`) turns the precondition into the answer.
`closeWithOpen` is the arm that benefits: apart from the class's own bits and the cells the
invariant names, its only premise was that callee precondition.

## The states that had no arm, and the arms that supply them

The census this module recorded had holes: head states the switch sends to a refusal or a
route no constructor's class admitted, so `WalkContinueFacts` and `WalkLoopEnd` could not
be total at them.  Each is now an arm of its own, at both levels, with its own producer and
price — and the first two are the delimitation boundary's, which is where the lengths are:

* **`}` (125) at depth zero** — `.closeBraceZero`.  `LeafBlock15` tests `%8 = 125` and
  takes `if.then53.i`, which tests `%sp = 0` and takes `if.then56.i`: the same store of the
  entry's position at `%e + 8` the closing bracket's refusal makes, through *different
  pivots* (`NodeBlock17 → LeafBlock15` against the bracket's `NodeBlock11 → LeafBlock9`).
  The routes are both six links to `if.then`, so the count is not what separates them — the
  blocks are, and `bracketRefuse_at` reads `%SwitchLeaf10` (`eq %8, 93`) and `%Pivot12`
  (`slt %8, 93`) by name while `closeBraceZero_at` reads `%SwitchLeaf16` and `%Pivot18`.
  The arms whose class bits admitted the byte — `classC` (`110 ≤ %8 ≤ 125`) and `run` (the
  tag test clear) — demand a head segment to `if.else387.i`, the default arm's path, which
  this byte does not take; `closingZero`/`closeBracketZero` are byte-pinned to `93`, and
  `closeWithOpen` requires `%sp ≠ 0`.  So the state was reachable
  by no arm, and the byte's own arm is the one that reaches it: six links, priced at
  `6 + 2 ≤ 32` inside one entry's allowance, with the word `refuseSegment_word_of_store`
  reads back at the store the run took.
* **A container opener at depth `520`** — `.openAtCap`.  `if.end.i`'s `ugt %sp.i.0248, 519`
  is taken at the stacks' staged extent, so the run leaves the opener route for
  `if.then21.i`'s offset store and the copy.  `WalkInv.depth_cap` bounds the depth by
  `stage2StackExtent = 520` and nothing below it, and `containerOpen`'s `hsp519` is the
  split's premise, so at `520` that arm was uninhabited; `JsonStage2WalkTerminalPrice`'s
  `.containerOpen` row records the same boundary.  The arm is `[` and `{` at depth `520`
  alone — one arm for both bytes, since both reach `if.then.i` — seven links from the head,
  priced at `7 + 2 ≤ 32`, with the value-position call's row at the root slot's witness
  word and the call's answer `1` carried exactly as `.containerOpen` carries them and `C.sp =
  `520` in place of `C.sp ≤ 519`.
* **A container opener whose value-position answer is `0`** — `.containerOpenRefuse`.  The
  class `91`/`123` is the census's byte, but `if.then.i` branches on the call's answer: the
  `1` arms are `.containerOpen` (depth at or below `519`) and `.openAtCap` (`520`), and the
  `0` arm is `if.then16.i` — the refusal's offset store — which neither enumeration had a
  constructor for.  The answer is the *state's*: the callee's model returns `0` or `1`
  (`s2ValuePos_ret_zero_or_one`), and the branch takes the bit.  The arm is `[` and `{` at
  either depth when the answer is `0` — one arm for both bytes and all depths, since
  `if.then16.i` reads neither the byte nor the depth — six links from the head, priced at
  `6 + 2 ≤ 32`, with the call's row at the root slot's witness word.  With it the class is
  total over the invariant's states as well as over its bytes: the two answers are the
  whole of the branch, and each has its arm.

The third state is one byte, one nesting or one call's answer away from an ordinary
document, so none is excluded by the input domain: `"}"`, 520 nested `[` and a second
top-level value (`[0][`; its opener's answer is `0` at the slot the first value's close set)
are admitted, malformed and deeply-nested inputs.  That is why the arms were owed rather
than the domain narrowed.

With them the census is total over those bytes and depths, **and now over the states
too**: the string opener at a positive depth has its own pair of arms,
`HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`
(`JsonStage2WalkDispatchHcontStringDeep`).  `HcontClass.stringOpener` is the byte `34`; at
`C.sp ≠ 0` the head leaves `if.then219.i` for `land.lhs.true.i`, where `%ctype.i`'s and
`%cst.i`'s bytes at `%sp - 1` select the key bit at `if.end245.i` — the merge (the key
record, kind `5`, and the key's own branch `if.then330.i`) or the refusal at
`if.then249.i`.  The invariant admits the state (`depth_cap` bounds the depth above only)
and so does the document (`["`·`a`; `stringOpenAboveZero_reachable`), and the arm's
producer derives the class's own premises — the byte, the depth split and (at a positive
depth) the value-position staging — off the invariant.  Its route's *segment* is the row
it still takes, as `.twoEntry`'s body call and `.letters`' tail are theirs; the refusal
half of the route is composed (`stringDeepRefuse_at`).
`JsonStage2WalkHcontSeamInv` produces the seam states' invariants the tail producers read,
so those are not rows either.  What remains supplied per class is the arm's *payload*, the
table below's rows.

## The rows the remaining classes take, and from which producer

The class is the arm's own, so no row here is another arm's class.  **ABI** is a callee's
precondition or answer at the arm's argument list; **document** is the input's content read
as a value; **traversal** is the scan's round, guard and byte facts.

| level | class | producer | row that stops the derivation | kind |
|---|---|---|---|---|
| both | `.ws` (`126`/`127`, entry left) | `hcontFacts_of_staging` | `hlt125`/`hne125`; the stop's budget conjunct; `hTail`'s three calls | document, ABI |
| both | `.cleanup` (`126`/`127`, last entry) | `hcontCleanupFacts_of_staging` | the class's head bits and `hb` (the route of the byte before the entry's end); `hTail` | document, ABI |
| both | `.twoEntry` (`"`, entry left, `C.sp = 0`) | `hstringFacts_of_staging` | `s2_string_body`'s staging: the allocator cursor's placement, the log's arena word, the byte spacing, the escape count's sign bound; the next lane.  The row is the depth-zero edge's — `strPath8`'s `hsp0` parameter — and the bundle carries no depth field | ABI, document |
| both | `.stringOpenAboveZeroMerge`, `.stringOpenAboveZeroRefuse` (`"`, entry left, `C.sp ≠ 0`) | `hcontArm_stringOpenAboveZeroMerge_of_staging`, `…Refuse_of_staging` | the class's own facts are derived (the byte from `cont_reg8`, the two stack bytes from the carry's maps, the value-position staging from `tyBytes`/`stBytes`); the **route's segment** is the row — the merge's, whose blocks are the reservation, the body's call, the answer's tests, the record and `if.then330.i`.  The refusal half is composed (`stringDeepRefuse_at`, two links from `if.end245.i`'s state) | ABI, segment |
| both | `.scalar` | `hcontScalarFacts_of_staging`, `lastEntryArm_scalar_of_staging`; at the continuing head `hcontArm_scalar_of_rows` (`JsonStage2WalkDispatchScalarRows`) | the root word's zero; the last byte's class; the three calls — their preconditions and answers at the returned memories.  At the continuing head the seam's invariant and the tail are produced, so the row is the document row, the lane word and its read, and the three call rows | document, ABI |
| last | `.highByte` (`126`/`127`) | `hlastFacts_of_staging` | `HlastResidue`: the head bits, the last byte's class, the root word, the three calls | document, ABI |
| both | `.containerOpen` (`[`, `{`, answer `1`, depth `≤ 519`) | `containerOpenMerge_at` | the `519` boundary (above); the call's row at the root slot's witness word | document, ABI |
| both | `.openAtCap` (`[`, `{`, answer `1`, depth `520`) | `containerOpenCap_at` | `C.sp = 520` and the same witness row | depth, ABI |
| both | `.containerOpenRefuse` (`[`, `{`, answer `0`) | `containerOpenRefuse_at` | the call's row at the witness word and its answer `0` — the answer is the state's and the two arms split it | ABI |
| both | `.letters`, `.fLetter` | `hcontArm_letters_of_staging`, `hcontArm_fLetter_of_staging`; at the continuing head `hcontArm_letters_of_rows`/`hcontArm_fLetter_of_rows` (`JsonStage2WalkDispatchLettersRows`) | the three call rows at the seam, and the head's root-slot read: the seam's invariant, its two test cells and the root word's transport are the chain's (`contSeamMid_ee`, `contSeamMid_cond`, `contSeamMid_rootRead`), and the tail is `emptyTail_of_cells`'s | ABI, document |
| both | `.classC` (`110 … 125`) | `hcontArm_classC_of_staging`; at the continuing head the four leaves' `hcontArm_classC_56True_of_rows` … `walkDispatch_at_classC_58Else_of_rows` (`JsonStage2WalkDispatchClassCLeaves`) | the three call rows, and no seam row: the span's endpoint is one of four named states (`ClsS413T` `110`, `ClsS413F` `111 … 115`, `ClsS58T` `116`, `HeadS413` `117 … 125`), so its `HcontSeamCells` are produced at each (`classCSeamCells_56True` … `…_58Else`) from the leaf's span, its `phi` incoming and the chain's data; the byte's own span is `classCSpan_at`'s, and the tail is produced from those cells | ABI, document |
| continuing | the default arm's leaf document bytes (`.lowLeaf`, `.highLeaf`) at the classes whose span is `letters`/`fLetter`/`classC`, and at `.cleanup` | `JsonStage2WalkDispatchLeafBytes` | **closed for the six head-switch classes and the high-byte route**: `contByteSegScanFree`/`contByteSegLow`/`contByteSegHigh` state the byte's three pivot routes from any state at `NodeBlock41`, `contSwHeadLeafSeg` composes them after the class's prefix and the shared four, and `contLowHeadLeafSeg` … `contBrcHeadLeafSeg` are the six classes' chains; the six `*HeadChain_of_lane` producers take `HcontHeadByte` (the three non-whitespace classes) and dispatch, so a row's `.lowLeaf`/`.highLeaf` now has a head chain at every default class.  `hcontHeadLeafSeg` is the high-byte route's chain at the same three classes.  What is *not* yet composed is `.cleanup`'s **arm**: the class's bundle (`HcontCleanupFacts`) still asserts the scan-free bits, so the leaf routes have a chain to the seam but no bundle above it | document |
| continuing | `.run` | `runFacts_of_staging`; at the continuing head `hcontArm_run_of_row`/`hcontArm_run_of_class` (`JsonStage2WalkDispatchClassRows`, `JsonStage2WalkDispatchClassCase`) | **no leaf is pinned**: the class's row is `HcontRunRow` — the prefix to `sw.default.i` with the shared four's cells, the check state's `HcontRunRows`, the run's body, and the byte's leaf (`HcontRunLeaf`) — and `hcontRunFacts_of_seam` joins the rows to the leaf's call rows, so the bundle's tail is `hcontScanTailAt_leaf`'s at the leaf.  The one segment the arm takes is the head byte's own leaf below `if.else387.i`, at its own count (`nS ≤ 5`), ending at the leaf's endpoint: `lettersSpan`, `fSpan` and the four class-C spans are each that cell, and the six leaf producers are `hcontRunLeaf_letters` … `_58Else` (`JsonStage2WalkDispatchClassCase`).  What the row's producer adds at a leaf is the leaf's three call answers and the landing built on them; the kind literal (`%.sink372`) is part of the memory the first call reads, so `102`/`110`/`116` have their own groups (`HcontSeamAbi.scanF`/`scan56True`/`scan58True`).  **The three `if.else405.i` leaves are not the emit arm's**: that edge writes the literal `0`, `od_scalar_value` answers `0` there (`stage2ScalarValue`'s first arm, `stage2ErrSetMsg`) and the walk leaves for `if.then432.i`, so the emit group has no inhabitant at that literal (`hcontSeamCalls_no_literal_zero`) and the leaves' supply is the refusal arm's — `HcontSeamAbi.scanRefuse` (`HcontSeamRefusal`: the two leading calls, the answer `0` and the record's memory) at `LetS413`/`ClsS413F`/`HeadS413` — which `JsonStage2WalkDispatchClassCase`'s `hcontSeamRefuseAt_letters`/`_56Else`/`_58Else` reads.  A `.run` bundle at those bytes is therefore not their arm: it needs `HcontRunLeaf`, whose `calls` is the emit group | document, ABI, traversal |
| last | `.run` | `runLastFacts_of_staging`, and now `runLastFacts_of_seam` (`JsonStage2WalkDispatchRunLastSeam`) | **the seam group is stated**: `HlastWsSeam` is the last run's seam at `hlastRunSeam` (the run's stop `k` as the token's end, the bound `c` as `%cond350.i`), with the invariant, the `phi`, the five static registers, the root word across the kind store, the two test cells, the carry's bounds and the scan's span; `hlastRunTail_of_seam` derives the scan tail from it and `runLastFacts_of_seam` builds the whole `RunLastFacts` from the group, the head chain, the byte's span and the latch.  The bundle no longer *stands at* the staging.  What remains at this level is the **head** document byte's class: `HlastFacts` asserts the scan-free bits, so the last default arms' chains are not yet total over `.lowLeaf`/`.highLeaf` | traversal, document, segment |

The head chains and the spans are **derived in principle** — the segment lemmas
(`hlastTailSeg`'s eleven links, `walkHeadChainCSeg`, `hlastPrefixSeg`) compose them from
the class's bits and the endpoint cells — but no lemma exposes one as a segment apart from
the tail's three calls, so the producers take them beside `hTail`.  Retiring them moves
work, not closure: `hTail` remains, and it is the row that blocks the spans.

The **seam states' invariants**, which the tail producers take as `hInvT`/`hInvS`, are no
longer parameters in the same sense: `JsonStage2WalkHcontSeamInv` produces each of the
three (`ContTailStartC`'s from `hcontSpan17_of_cleanup`'s `n ≤ 17` links,
`scSeamByte`'s from the scalar route's `8 + hlastByteCount hb` — the prefix's eight and
the byte's route — and `TailStartC`'s from `hlastTailSeg`'s sixteen) as the head
chain's own `inv'`.  So a producer that has the class's head facts can reach the tail's
three calls without assuming the seam's invariant; what it still takes is `hTail`'s calls
themselves.

The calls' *preconditions* are a different matter from their answers, and the difference
is where the remaining work sits.  `s2ValuePosPre` and `s2AfterValuePre` ask for a stack
byte at or below the depth — `WalkInv.tyBytes`/`stBytes` covered by the mark, which is
`s2AfterValuePre_of_inv`'s argument.  What a producer of `.scalar`, `.containerOpen` or
`.letters` still owes is the chain: the answer from `answers`, the postcondition from
`sound`, the frame from `framed`, and the next call's precondition at the memory the
previous one left.  That is work over the helper contracts at each call memory, not a
missing input — and it is what `JsonStage2StringStageFacts` already does once for
`s2_string_body` (`s2StringBodyPre_at_string_call`).

## The price, at a document the walk admits

The run class's price row used to be the entry allowance's form,
`N + 4 * (c - 1 - i) ≤ 6` — `terminalPriceFits` at the document's numbers.  At
`"abcdefgh "` the terminal run is eight links, so that row is false at the document's own
numbers, and no producer that read `N`, `c` and `i` from the document could state it: the
row was a restriction on the input, not a fact about it.

The row is now derived rather than excluded.  `RunLastFacts` carries the three things the
document does supply — the run's count inside the bytes the entry has left (`hNdoc`), the
run's start at the entry's position (`hstart`) and the scan's bound inside the document
(`hspanDoc`) — and `runLastMerge_at` spends them through `runLast_price_with_credit`, whose
credit form `6 + 8 * (n - ix)` pays the same document.  What closed the gap was restating
`mergeLast`'s price at the credit boundary (`boundary G G.nep = G.n`), which the dispatch
now states; the theorem below is what the *old* form says at that document, and it is the
reason the general form exists.
-/
import LeanLLVM.Refinement.JsonStage2WalkTerminalPrice
import LeanLLVM.Refinement.JsonStage2WalkDispatchRefusalsOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosersOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchPair

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The closing delimiter's callee precondition, from the stacks -/

/-- **`s2_after_value`'s precondition at the walk's own arguments.**  The call's first
argument is the emitted `%sub.i`, the depth less one (`pairOff_eq`); above zero the callee
reads the type stack's byte below that index, and `WalkInv.tyBytes` covers it because the
mark is at or past the depth (`sp_le_wlen`) and the depth is a small numeral
(`depth_cap`, `depth_lt_32`).  So the precondition is a theorem at every positive-depth
state, and the call's answer is `s2AfterValue_answers`'s. -/
theorem s2AfterValuePre_of_inv {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hsp : C.sp ≠ 0) :
    s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next := by
  have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
  have h32 : C.sp < 2 ^ 32 := depth_lt_32 hInv.depth_cap
  have hoff : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 :=
    pairOff_eq hpos h32
  have hlt : C.sp - 2 < C.wlen := by
    have h := hInv.sp_le_wlen
    omega
  refine ⟨BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295, G.next0 + 8,
    C.stage.ctype, C.stage.cst, rfl, Or.inr ?_⟩
  rw [hoff]
  have he : C.sp - 1 - 1 = C.sp - 2 := by rw [Nat.sub_sub]
  rw [he]
  exact ⟨C.tyMap (C.sp - 2), hInv.tyBytes (C.sp - 2) hlt⟩

/-! ### The classes whose rows are all derived -/

/-- **The continuing census's classes that need nothing beside the invariant.**  The
comma's and the colon's bytes take their refusal or their above-depth pair by the depth's
own split; the closing bracket takes its refusal with nothing open and the nesting check
with a container open; the closing brace takes its refusal at zero and the nesting check
above it, which requires one.  Every one of those bytes has an arm at every depth the
invariant admits, so the class is the byte test alone. -/
def DerivedHcontClass {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Prop :=
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1

/-- **The last-entry census's classes that need nothing beside the invariant.**  The
continuing head's four bytes, and the bare string opener, which at this level is a refusal
rather than the two-entry path's class. -/
def DerivedLastClass {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Prop :=
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1 ∨
  evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1

/-- **The continuing entry's arm, at the derived classes.**  Every arm here is the class's
own producer at the state: the class's byte test pins the `%8` cell, the depth's split is
decided, and the remaining cells are the invariant's own.  The evidence is a `Nonempty`,
not a bare inhabitant, because the class is a disjunction: `Or` does not eliminate into
the arm's `Type`, and the dispatch below eliminates the proposition instead. -/
theorem hcontArm_of_derivedClass {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (h : DerivedHcontClass G C) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  rcases h with h44 | h58 | h93 | h125
  · by_cases hsp : C.sp = 0
    · exact ⟨hcontArm_commaZero_of_staging C s hInv h44 hsp⟩
    · exact ⟨hcontArm_commaAboveZero_of_staging C s hInv h44 hsp⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨hcontArm_colonZero_of_staging C s hInv h58 hsp⟩
    · exact ⟨hcontArm_colonAboveZero_of_staging C s hInv h58 hsp⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨hcontArm_closeBracketZero_of_staging C s hInv h93 hsp⟩
    · exact ⟨hcontArm_closeWithOpen93_of_staging C s hInv h93 hsp
        (s2AfterValuePre_of_inv hInv hsp)⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨hcontArm_closeBraceZero_of_staging C s hInv h125 hsp⟩
    · exact ⟨hcontArm_closeWithOpen125_of_staging C s hInv h125 hsp
        (s2AfterValuePre_of_inv hInv hsp)⟩

/-- **The last entry's arm, at the derived classes.**  The count is exhausted, which the
bare opener's refusal reads (`quoteCount_ge`); every other arm is the continuing one's
term at this level's constructor. -/
theorem lastEntryArm_of_derivedClass {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hnot : ¬ (C.k + 1 < G.nep))
    (h : DerivedLastClass G C) :
    Nonempty (LastEntryArm (stage2Calls stage2SubCalls) G C s) := by
  rcases h with h34 | h44 | h58 | h93 | h125
  · exact ⟨lastEntryArm_stringOpener_of_staging C s hInv h34 hnot⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨lastEntryArm_commaZero_of_staging C s hInv h44 hsp⟩
    · exact ⟨lastEntryArm_commaAboveZero_of_staging C s hInv h44 hsp⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨lastEntryArm_colonZero_of_staging C s hInv h58 hsp⟩
    · exact ⟨lastEntryArm_colonAboveZero_of_staging C s hInv h58 hsp⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨lastEntryArm_closeBracketZero_of_staging C s hInv h93 hsp⟩
    · exact ⟨lastEntryArm_closeWithOpen93_of_staging C s hInv h93 hsp
        (s2AfterValuePre_of_inv hInv hsp)⟩
  · by_cases hsp : C.sp = 0
    · exact ⟨lastEntryArm_closeBraceZero_of_staging C s hInv h125 hsp⟩
    · exact ⟨lastEntryArm_closeWithOpen125_of_staging C s hInv h125 hsp
        (s2AfterValuePre_of_inv hInv hsp)⟩

/-- **The continuing entry's dispatch, at the derived classes.**  The arm through
`HcontArm.dispatch`, at the continuing entry's guard.  This is the shape the loop's step
reads, so at these bytes the step needs no supply. -/
theorem walkDispatch_of_derivedClass {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (h : DerivedHcontClass G C) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨a⟩ := hcontArm_of_derivedClass hInv h
  exact HcontArm.dispatch hInv hblock hk a

/-- **The last entry's dispatch, at the derived classes.**  The arm through
`LastEntryArm.dispatch`, at the negated count. -/
theorem walkDispatchLast_of_derivedClass {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hnot : ¬ (C.k + 1 < G.nep)) (h : DerivedLastClass G C) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨a⟩ := lastEntryArm_of_derivedClass hInv hnot h
  exact LastEntryArm.dispatch hInv hblock hnot a

/-! ### The price row, at a document the walk admits -/

/-- **The entry-only allowance is false at `"abcdefgh "` — and the general price covers
it.**  The old row was `N + 4 * (c - 1 - i) ≤ 6` at the state's numbers, with
`RunLastFacts` carrying the ties that name them; the bundle no longer states it, and this
theorem is the arithmetic that retired it.  At eight continuing bytes in one entry the
terminal run is eight links, so the six-link form is false at the document's own numbers —
it was a restriction on the input, not a fact about it.  `JsonStage2WalkTerminalPrice`'s
credit form pays the same document, and `RunLastFacts` now carries that document's bounds
(`hNdoc`, `hstart`, `hspanDoc`) with `runLastMerge_at` spending them. -/
theorem entryOnlyBudget_false_at_eight {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {f : RunLastFacts G C s}
    (hbs : G.bs = [97, 98, 99, 100, 101, 102, 103, 104, 32])
    (hpos : entryPos G C.k = 0)
    (hix : entryPos G C.k ≤ f.i) (hk : f.i = terminalStop G.bs (entryPos G C.k))
    (hc : f.c = G.n) (hN : f.N = f.i - entryPos G C.k) :
    ¬ (f.N + 4 * (f.c - 1 - f.i) ≤ 6) := by
  refine terminalPrice_no_runLastFacts (f := f) hix hk hc hN ?_
  rw [hbs, hpos]
  exact terminalPrice_eight_outside.1

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.s2AfterValuePre_of_inv
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_of_derivedClass
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_of_derivedClass
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_of_derivedClass
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatchLast_of_derivedClass
#print axioms LeanLLVM.Refinement.WalkScope.entryOnlyBudget_false_at_eight

end WalkScope
end LeanLLVM.Refinement
