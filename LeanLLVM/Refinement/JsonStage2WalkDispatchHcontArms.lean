/-
The continuing entry's dispatch: one arm per head-switch class, and the census.

## What was wrong

`WalkContinueFacts` (this module's, beside the arm) asked for `HcontCase` at every
head state with an entry left.  `HcontCase`'s three arms are the whitespace and scan-free
one-entry bundles — both of which require the head byte to be `126` or `127` — and the
standalone string, which requires `34`.  `JsonStage2WalkHcontDomain` refutes that split at
the document `"01"`: byte `0x30` is no arm's class, so an ordinary numeral at a non-last
entry had no continuing evidence and the branch was vacuous there.

## The census

`HeadArm` (`JsonStage2WalkDispatchArms`) is the head switch's arms as a value, and
`HeadArm.complete` says every byte has exactly one.  The continuing entry's class is that
arm together with the tag test at the token's end (`if.end372.i`'s `%or.cond677.i`), which
is the emitted test that selects the plain-value route:

```text
%or.cond677.i = (%8 == 45) || ((%8 + 208) u< 10)
```

`HcontClass` is that census: `HeadArm`'s constructors, with `defaultValue` split into the
tag's two values.  `HcontClass.complete` proves every byte has one — the tag test is one
bit, so the split is `HeadArm.complete` beside the bit's two values, exactly as
`HeadArm.complete` itself is built.  It is exhaustive over the emitted dispatch *by
theorem*, and no class borrows another's byte test.

## The evidence, per class

`HcontArm` is the dispatch's evidence, one constructor per class the layer proves or
supplies, and `.dispatch` turns it into the actual `WalkDispatchResult`:

* `.ws` — `HcontFacts`, the whitespace-run class: its run, seam, tail and scan compose
  through `walkDispatch_at_continue_cells_ws` (the high-byte route).
* `.cleanup` — `HcontCleanupFacts`, the same route's no-run class, through
  `walkDispatch_at_continue_cells`.
* `.twoEntry` — `HstringFacts` beside its `HstringResidue` and the arm's own
  selector, the standalone string, through `WalkDispatchResult.ofStringMerge`.  The
  residue is the state's, so the loop's step no longer takes `WalkStringResidue` beside
  the continuing premise: it is an arm's field.  The selector is the arm's rather than
  the residue's because the same call can refuse: a refusing body leaves `NodeBlock31`
  at `cleanup339.critedge.i`, which is not this merge.

  **This arm is the string opener at depth zero**, and the depth split is now a parameter
  of the theorems that read it rather than a field of the bundle: `strPath8`/`strPath9`/
  `stringPath_seg`/`ofStringMerge` take `hsp0 : C.sp = 0`, which is what makes the
  `if.then219.i` edge the `if.end245.i` one.  At positive depth the same byte's head leaves
  that block for `land.lhs.true.i`, and the two marker bytes at `%sp - 1` (`%ctype.i`'s and
  `%cst.i`'s) decide the merge (`if.end256.i`, the key record's kind `5`) or the refusal at
  `if.then249.i` — that route is
  `HcontArm.stringOpenAboveZeroMerge`/`.stringOpenAboveZeroRefuse`
  (`JsonStage2WalkDispatchHcontStringDeep`), the two constructors beside this one.
* `.stringOpenAboveZeroMerge` / `.stringOpenAboveZeroRefuse` — **the same byte above depth
  zero**: `if.then219.i`'s depth edge, `land.lhs.true.i`'s marker and `if.then231.i`'s
  state byte, then `if.end245.i`'s selection.  The route is the merge when the nest's
  `%or.cond523.i` is set (the reservation, the body's call, the answer's tests, the record
  and the key's own branch `if.then330.i`), and the refusal at `if.then249.i` when it is
  clear.  What the constructors carry is the class's own facts — the byte, the depth
  split, the two stack bytes, the value-position call's answer — and the route's segment
  with its predecessor and index; the merge's segment is the class's row
  (`stringDeepRefuse_at` composes the refusal from `if.end245.i`'s state, and the head's
  marker links are `walkLandLhsTrue_at`/`walkIfThen231_at`).
* `.scalar` — **`HcontScalarFacts`**, the plain-value class on the numeral route: the
  head's four scalar pivots, the count test's succeeding arm, the byte's own route below
  `if.else387.i` and the tag test's true arm, composed through
  `walkRevolutionMergeSegScalar` (`JsonStage2WalkHcontScalar`).  This is the class the old
  split excluded, and it is proved — not supplied — so the document `"01"`'s head is a
  merge arm.  Its producer is `hcontArm_scalar_of_staging`
  (`JsonStage2WalkDispatchScalarOfStaging`), which derives the `%8` cell, `h91`, the
  counts, the lane's pointer, the entry's index, the token record's cells and the byte
  before the entry's end with its read, and carries the byte's route
  (`HcontScalarPrefix.hb`).
* `.closeBracketZero` — `if.then53.i` at depth zero on the **continuing** head: `]` with
  nothing open is refused (`bracketRefuse_at`'s chain; its only count premise is the head's
  guard, which a continuing entry has).  It is proved rather than supplied, and the last
  entry has the same arm.
* `.closeBraceZero` — the same two refusal blocks at `}`, on the continuing head: the byte
  reaches `if.then53.i` through `NodeBlock17 → LeafBlock15`, so the arm is the bracket
  refusal's count at its own pivots (`closeBraceZero_at`).  Before it existed the byte at
  depth zero was in no constructor's class at either level
  (`JsonStage2WalkDispatchResidual` records that history), so it is the continuing
  census's second formerly-missing arm beside `.openAtCap`.
* `.commaZero`, `.colonZero` — the comma's and the colon's depth-zero refusal on the
  continuing head: six links each (`commaRefuse_at`, `colonRefuse_at`), the same two the
  last entry has.  The documents `,0` and `:0` take them.
* `.commaAboveZero` — the comma with an entry left and a container open, on the
  continuing head: the container pair's four sub-routes (`commaBraceMerge_at`,
  `commaBraceRefuse_at`, `commaBracketMerge_at`, `commaBracketRefuse_at`), eight links
  each.  The continuing guard is the loop's, not this arm's.
* `.colonAboveZero` — the colon with an entry left and a container open: the marker's
  three sub-routes, the brace pair at eight links (`colonBraceMerge_at`,
  `colonBraceRefuse_at`) and the marker's own refusal at seven (`colonMarkerRefuse_at`).
* `.containerOpen` — `[` and `{` on the continuing head: both enter `if.then.i`, and the
  four head links beside the tail's five reach the merge — nine links
  (`containerOpenMerge_at`).  The documents `[0]` and `{"a":1}` take it.
* `.openAtCap` — the same two bytes at the stacks' staged extent, on the continuing head:
  `if.end.i`'s `ugt %sp.i.0248, 519` is taken at `520`, so the run is the head's four
  links, the value-position call, the guard's true arm and `if.then21.i`'s offset store to
  the copy — seven links, `containerOpenCap_at`, priced at `7 + 2 ≤ 32`.  `containerOpen`'s
  `C.sp ≤ 519` is the other side of the same test, so the two arms divide the depths the
  invariant admits and neither covers the other's.
* `.containerOpenRefuse` — the same two bytes at the reason the class was once only total
  over its bytes: `if.then.i`'s call answers `0`, so the branch is `if.then16.i`'s offset
  store and the copy — six links, `containerOpenRefuse_at`, priced at `6 + 2 ≤ 32`.  The
  answer, not the byte and not the depth, selects it, and the callee's answer is always `0`
  or `1` (`s2ValuePos_ret_zero_or_one`), so this constructor is what makes the class total
  over the invariant's states.  Its word is the root slot's witness, the same witness the
  `1` arms carry, and no clause names the value.
* `.closeWithOpen` — `]` and `}` with a container open, at the continuing head: both enter
  `if.then53.i`, and the nesting check's two stack bytes select the merge or a refusal —
  `closeWithOpen_at`'s four sub-routes.  The continuing guard is the loop's, not the arm's:
  the merge keeps the depth and advances the index by one, so the entry after the
  delimiter is the next iteration's.
* `.letters` — the default arm's letter and high-byte route on the scan-free class:
  `lettersSpan`'s four links below `if.else387.i` (`NodeBlock62`, `LeafBlock54`,
  `if.else405.i`, `if.then413.i`), with the head's chain to the seam and the tail's three
  calls as their own counted segments (the head class's `nH ≤ 12`, and three) and the
  merge's own step — at most twenty links, `lettersCleanupMerge_at`.  The class premise is
  explicit (the tag test clear,
  `slt %8 110 = 1`, `%8 ≠ 102`), so the chain the reader must supply is the class's.
* `.fLetter` — the byte `102` (`'f'`) on the scan-free class: `LeafBlock54`'s *true* arm,
  `if.then397.i`'s empty body to `if.then413.i` (kind `9`) rather than the letters route's
  `if.else405.i`.  `fSpan`'s four links and `fCleanupMerge_at`'s merge — twenty links.
* `.classC` — the class-C span's leaves on the scan-free class, the bytes `110 … 125`:
  `110` via `LeafBlock56`'s true arm (`if.then403.i`, kind `10`), `111 … 115` via its else
  arm, `116` from `LeafBlock58` itself (kind `8`) and `117 … 125` via its else arm.  The
  span is the byte's own `Seg` (`c56TrueSpan`, `c56ElseSpan`, `c58TrueSpan`,
  `c58ElseSpan`) at `nS ≤ 5`, and `classCMerge_at` composes the tail and the merge.
* `.run` — **the default arm's run class**, at every default span: the byte before the
  entry's end is whitespace, so the token's end is the run's stop and the extra-token scan
  is entered.  `RunFacts` carries the path's inputs and `runScanMerge_at` composes the
  segment, the visits by `scanRoundsAt` — the rounds at the seam's own bound, which
  `JsonStage2WalkRevolutionSeg`'s class-C-only `scanWsRounds` is not.

**The byte census is exhaustive, and the arm is total over the invariant's states.**  The
head switch's bytes are `HeadArm.complete`'s and the tag test's two values are
`HcontClass.complete`'s: every byte has exactly one class, by theorem, and the
run/scan-free split is carried by each arm's own tail
(`.letters`/`.fLetter`/`.classC` end at `if.end473.i`, `.run` at `land.rhs457.i`, and
`.ws`/`.cleanup` are `126`/`127`'s two).  `126` and `127` are
`HcontClass.defaultValueHigh` and `HcontArm.ws`/`.cleanup`'s class: both bundles carry
the four bits that leave exactly those two bytes, and both arms are proved with their
counted segments (`walkRevolutionMergeSegWs`, `walkRevolutionMergeSeg`).

The states the split once had no arm for are four, and all four are covered:

* `}` at zero — `.closeBraceZero` (`NodeBlock17 → LeafBlock15` to `if.then53.i`'s
  refusal);
* an opener at the stacks' staged extent — `.openAtCap` (`if.end.i`'s `ugt` taken at
  `520`);
* an opener whose value-position answer is `0` — `.containerOpenRefuse` (`if.then.i`'s
  branch to `if.then16.i`'s offset store).  The class `91`/`123` is the census's byte, but
  `if.then.i` branches on the call's answer and it is the state's: `1` takes `.containerOpen`
  or `.openAtCap`, `0` takes this arm, and `s2ValuePos_ret_zero_or_one` says the answer is
  one of the two.  So the class is now total over the invariant's states as well as over
  its bytes, and the root slot's value — a witness word the arms carry, not a clause —
  is not what the split turns on;
* the string opener at a positive depth — `.stringOpenAboveZeroMerge` and
  `.stringOpenAboveZeroRefuse`.  `HcontClass.stringOpener` is the byte `34`, and at
  `C.sp ≠ 0` the head leaves `if.then219.i` for `land.lhs.true.i`, reads `%ctype.i`'s and
  `%cst.i`'s bytes at `%sp - 1` and selects the key bit `if.end245.i`'s `phi` carries.
  The class's premises are the byte, the depth split and the two stack bytes, and the two
  producers (`hcontArm_stringOpenAboveZeroMerge_of_staging`,
  `hcontArm_stringOpenAboveZeroRefuse_of_staging`) derive the byte from `cont_reg8` and the
  stack bytes from the carry's maps at `WalkInv.tyBytes`/`stBytes`; the value-position
  call's staging is the caller's, at the state's own root word, which `HcontOpenCall`
  carries.  The document `["`·`a` takes it
  (`stringOpenAboveZero_reachable`), and the same document's seed head is the control
  (`stringOpenAboveZero_absent_at_seed`: depth zero, byte `91`).

So no admitted state is outside the enum.  What each class still supplies is its *route*,
where the route is not a theorem yet: for the new pair that is the merge's counted
segment (the body's call sits in it, and `s2StringBodyPre`'s producer is the string
staging) — exactly the grade the residual table records for `.letters`' head chain and
`.twoEntry`'s body call.  Nothing is refuted and no class is narrowed to make another's
premise collapse.

Each constructor carries only its own arm's premises, and the price is the dispatch's own
(`WalkDispatchResult`'s), so no class's byte restriction is a premise of another's.

## Why the token-end class is not part of the census

The head switch's tests are on the entry's first byte (`%8`), and the tag test is the same
byte's.  The whitespace run is decided by the byte before the *entry's end* (`%35`), which
is the document's content rather than the head state's dispatch; so it is each one-entry
arm's own premise (`HcontFacts.hClass`, `HcontCleanupFacts`'s `hb : HcontByteRoute`,
`HcontScalarFacts`'s three), not a second classification over `%8`.  The two are different
questions, and this module keeps them apart exactly as `JsonStage2WalkDispatchArms` keeps
the last entry's guard apart from its head switch.
-/
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar
import LeanLLVM.Refinement.JsonStage2WalkHcontWsScalar
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkDispatchLetters
import LeanLLVM.Refinement.JsonStage2WalkDispatchFLetter
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC
import LeanLLVM.Refinement.JsonStage2WalkDispatchRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchArms

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing entry's head census -/

/-- **The continuing entry's class**, as the emitted head dispatch computes it: the head
switch's arm (`HeadArm`), with the default arm split by `if.end372.i`'s tag test.  Every
constructor but `value`/`otherValue` is `HeadArm`'s; the two split `HeadArm.defaultValue`,
which is exactly the arm whose bytes can satisfy the tag test. -/
inductive HcontClass (x : BitVec 8) : Prop
  /-- `%8 = 34`: the string opener, the two-entry token. -/
  | stringOpener (h : evalICmp .eq x (BitVec.ofNat 8 34) = 1)
  /-- `44 ≤ %8 < 58` and `%8 = 44`: the comma. -/
  | comma (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 44) = 1)
  /-- `44 ≤ %8 < 58` and `%8 = 58`: the colon. -/
  | colon (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 58) = 1)
  /-- `91 ≤ %8 < 123` and `%8 = 91`: the open bracket. -/
  | openBracket (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
      (h : evalICmp .eq x (BitVec.ofNat 8 91) = 1)
  /-- `91 ≤ %8 ≤ 122` and `%8 = 93`: the close bracket. -/
  | closeBracket (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 93) = 1)
  /-- `123 ≤ %8 ≤ 124` and `%8 = 123`: the open brace. -/
  | openBrace (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
      (h : evalICmp .eq x (BitVec.ofNat 8 123) = 1)
  /-- `%8 = 125`: the close brace. -/
  | closeBrace (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 125) = 1)
  /-- `HeadArm.defaultValue` with the tag test set: the plain-value arm, a digit or `-`.
  This is `HcontScalarFacts`'s head class. -/
  | value (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
      (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
  /-- `HeadArm.defaultValue` with the tag test clear: the same head class, on the letters'
  route — `.`, `/` and the rest of `[45, 58) \ {45} ∪ {48..57}` excluded. -/
  | otherValue (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
      (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
  /-- `HeadArm.defaultValueLow`: `%8 < 91`, `%8 < 44`, `%8 ≠ 34`. -/
  | defaultValueLow (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
      (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
  /-- `HeadArm.defaultValueMid`: `%8 < 91`, `44 ≤ %8`, `58 ≤ %8`, `%8 ≠ 58`. -/
  | defaultValueMid (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
      (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
  /-- `HeadArm.defaultValueBracket`: `91 ≤ %8 < 123`, `%8 < 93`, `%8 ≠ 91`. -/
  | defaultValueBracket (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
      (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
  /-- `HeadArm.defaultValueBracketHigh`: `91 ≤ %8 < 123`, `93 ≤ %8`, `%8 ≠ 93`. -/
  | defaultValueBracketHigh (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
      (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
  /-- `HeadArm.defaultValueBrace`: `91 ≤ %8`, `123 ≤ %8`, `%8 < 125`, `%8 ≠ 123`. -/
  | defaultValueBrace (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
      (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
  /-- `HeadArm.defaultValueHigh`: the bytes 126 and 127, the preserved high-byte route. -/
  | defaultValueHigh (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
      (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)

/-- **Every byte has a continuing class.**  The head switch's census supplies the arm;
`HeadArm.defaultValue` is the only arm whose bytes can satisfy the tag test, and the bit's
two values split it.  The other arms' tag values are not needed: they are each *one* class
of the continuing dispatch, and the arm that carries them is the head route's — the two
bytes `126`/`127` are `HcontArm.ws`/`.cleanup`'s class and the string opener, the
delimiters and the container openers are their own arms', whichever value the bit has. -/
theorem HcontClass.complete (x : BitVec 8) : HcontClass x := by
  cases HeadArm.complete x with
  | stringOpener h => exact .stringOpener h
  | comma h44 h => exact .comma h44 h
  | colon h44 h58 h => exact .colon h44 h58 h
  | openBracket h91 h123 h93 h => exact .openBracket h91 h123 h93 h
  | closeBracket h91 h123 h93 h => exact .closeBracket h91 h123 h93 h
  | openBrace h91 h123 h125 h => exact .openBrace h91 h123 h125 h
  | closeBrace h91 h123 h125 h => exact .closeBrace h91 h123 h125 h
  | defaultValue h91 h44 h58 hne44 =>
      by_cases hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
      · exact .value h91 h44 h58 hne44 hbit
      · exact .otherValue h91 h44 h58 hne44 (bitZeroOfNeOne hbit)
  | defaultValueLow h91 h44 hne34 => exact .defaultValueLow h91 h44 hne34
  | defaultValueMid h91 h44 h58 hne58 => exact .defaultValueMid h91 h44 h58 hne58
  | defaultValueBracket h91 h123 h93 hne91 => exact .defaultValueBracket h91 h123 h93 hne91
  | defaultValueBracketHigh h91 h123 h93 hne93 =>
      exact .defaultValueBracketHigh h91 h123 h93 hne93
  | defaultValueBrace h91 h123 h125 hne123 =>
      exact .defaultValueBrace h91 h123 h125 hne123
  | defaultValueHigh h91 h123 h125 hne125 =>
      exact .defaultValueHigh h91 h123 h125 hne125

/-- **The document `"01"`'s head byte is the `value` class.**  The positive half of the
regression, at the census's own vocabulary: `0x30`'s four scalar pivots hold and the tag
test is `1`, so `HcontClass (ofNat 8 48)` is the plain-value arm — the class the old split
lacked and this census names. -/
theorem HcontClass.value_of_48 : HcontClass (BitVec.ofNat 8 48) :=
  .value (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### The evidence, per class -/

/-- **The continuing entry's dispatch, as the arm it took.**  One constructor per class
the layer proves or supplies; `.dispatch` is the function into `WalkDispatchResult`.

Each constructor carries only its own arm's premises: the whitespace bundle's class and
tail, the scan-free bundle's, the standalone string's residue, the plain-value bundle's
head class and tail supply, the closing bracket's own cells, and — for the arms whose
segments are still owed — that arm's counted segment and endpoint facts. -/
inductive HcontArm (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) : Type
  /-- The whitespace-run token on the high-byte route (`HcontFacts`). -/
  | ws (f : HcontFacts G C s) : HcontArm calls G C s
  /-- The scan-free token on the high-byte route (`HcontCleanupFacts`). -/
  | cleanup (f : HcontCleanupFacts G C s) : HcontArm calls G C s
  /-- **The standalone string, with its residue, its depth split and its accepting-arm
  selector.**  `R` is the two words the walk layer does not carry, and `hR8` is
  `NodeBlock31`'s test: the model's form is `1` or `2` on the accepting arms, and
  neither is `< 1` signed.  A refusing answer is a legal answer to the same call, so
  this is the arm's premise rather than the state's.  `hsp0` is `if.then219.i`'s edge:
  the block branches on the depth, and depth zero is the arm's own route — the same
  byte above depth zero leaves `land.lhs.true.i` and takes the marker links, which is
  `stringOpenAboveZero`'s route. -/
  | twoEntry (f : HstringFacts G C s) (hsp0 : C.sp = 0) (R : HstringResidue G C s f)
      (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0) : HcontArm calls G C s
  /-- **A string opener above depth zero, reaching the merge.**  The head is the byte
  `34` at a positive depth, so `if.then219.i`'s depth test leaves it for
  `land.lhs.true.i`, whose read of the type stack's byte at `%sp - 1` and
  `if.then231.i`'s read of the state stack's byte at the same index select the key bit
  of `if.end245.i`'s `phi`.  The route is the merge once the nest's `%or.cond523.i` is
  set: the reservation, the body's call, the answer's two tests, the record and the key's
  own branch `if.then330.i` to `cleanup478.i`.

  **What the arm carries.**  The class's own facts — the byte, the positive depth, the
  two stack bytes and the value-position call's staging and answer at the state's *own*
  root word (`rdv`, the slot's value as the block's load reads it) — and the route's
  endpoint: a counted segment to the merge, its block, the merge's predecessor
  `if.then330.i`, the index cell and the price.  The segment is the arm's to supply.
  Every link of it is proved (`if_end256_i`, `z_arena_reserve_exit`, `NodeBlock31_at`,
  `LeafBlock29_at`, `if_then281_i`/`if_else285_i_at`, `if_end290_i`, `if_then328_i`,
  `walkIfThen330_at`), and the rows that stop the composition are the seam's three cells
  (`%conv211.i`'s word, the cursor pin and the window bound) and the body's staging at the
  call's memory — the staging has a producer (`s2StringBodyPre_of_staging`) and the
  emitted body's contract (`s2StringBodyBody_contract`) makes the model the body's, so no
  clause is missing; the composition is.  Its source is the loop head, so the head chain
  to `if.then219.i` and the two marker links are part of the same segment, and that chain
  reads the document's next lane and the root slot's word.
  `stringOpenAboveZeroMerge_of_staging` is the producer. -/
  | stringOpenAboveZeroMerge {b1 b2 : UInt8} {rdv : BitVec 32}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)))
      (hsp : C.sp ≠ 0)
      (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2)
      (hpreV : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      (r : CallOutcome)
      (hcall : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
      (Cd : WalkCarry G) (sd : State) (p : Nat) (k2 : Nat) (nepv : BitVec 64)
      (hseg : WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
      (hblock : Cd.block = "cleanup478.i")
      (hkC : Cd.k = C.k)
      (prev : String) (hprev : prev = "if.then330.i" ∨ prev = "if.else334.i")
      (hpre : sd.pre = some prev)
      (hinc : lookupName sd.env "%inc208.i" = some (.int 64 (BitVec.ofNat 64 k2)))
      (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
      (hadvance : C.k < k2) (hcap : k2 ≤ nepv.toNat)
      (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) : HcontArm calls G C s
  /-- **A string opener above depth zero, refused at the nest's own test.**  The same
  class, with `%or.cond523.i` clear: `if.end245.i` leaves for `if.then249.i`, whose offset
  store and the copy are the refusal arm.  The route witness is `WalkRefuseAt`, the
  structure every refusing route in the tree states (`bracketRefuse_at`,
  `commaRefuse_at`, …), so the arm carries the refusal exactly as the other refusal arms
  do. -/
  | stringOpenAboveZeroRefuse {b1 b2 : UInt8} {rdv : BitVec 32}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)))
      (hsp : C.sp ≠ 0)
      (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2)
      (hpreV : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      (r : CallOutcome)
      (hcall : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
      (href : WalkRefuseAt (stage2Calls stage2SubCalls) G C s) :
      HcontArm calls G C s
  /-- **The plain-value token on the numeral route** (`HcontScalarFacts`): the class the
  old split excluded. -/
  | scalar (f : HcontScalarFacts G C s) : HcontArm calls G C s
  /-- **The plain-value token with a whitespace run at the document's byte**
  (`HcontScalarWsFacts`): the numeral's four pivots and the tag test's own `1` arm, the
  whitespace skip at `%35` and `if.end372.i`, and the scan tail its stop enters.

  This is the cell the route-carrying `.scalar` left empty.  `.scalar`'s `hb` is
  `HcontByteRoute` — the three non-whitespace leaves — and the whitespace byte is the
  run class's on the high-byte route (`HcontFacts`) and on the default arm (`RunFacts`),
  but neither bundle's head is this route's: `HcontFacts`'s prefix is the head chain's
  `contPrefixLand`, `RunFacts` takes the tag test's *clear* arm and its span below
  `if.else387.i`, and here the head is the numeral's and the seam is `if.then413.i`.  A
  numeral followed by whitespace is admitted by the header, so the census needed this
  arm: the run is restated at this prefix (`scWsRunF`) and its seam is the tag-true link
  (`scWsSeamSeg`), not the class-C span's.  `HcontScalarWsFacts` is the document's and
  the callees', and `walkDispatch_at_continue_scalarWs` composes the path to the merge
  with the merge's three cells — so the arm is proved, not supplied. -/
  | scalarRun (f : HcontScalarWsFacts G C s) : HcontArm calls G C s
  /-- **A closing bracket at depth zero, with nothing open**: refused at `if.then56.i`.
  The links are `JsonStage2WalkDispatchArms`'s `.closingZero` chain, and its only count
  premise is the head's guard, which a continuing entry has. -/
  | closeBracketZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **A closing brace at depth zero**, on the continuing head: the same refusal the
  bracket's arm states, reached through `NodeBlock17 → LeafBlock15` (`%Pivot18` is
  `slt %8, 125`, `%SwitchLeaf16` is `eq %8, 125`) rather than `NodeBlock11 → LeafBlock9`.
  Six links (`closeBraceZero_at`), and the last two blocks — the depth test and the offset
  store — are the bracket's because neither reads the byte.  The continuing guard is the
  loop's, not this arm's. -/
  | closeBraceZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **A comma at depth zero**, on the continuing head: nothing is open for it to
  separate, so `if.then127.i` sends the run to `if.then130.i`'s offset store and the
  refusal copy — six links (`commaRefuse_at`).  The only count premise is the head's
  guard, which a continuing entry has. -/
  | commaZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **A colon at depth zero**, on the continuing head: the same refusal at
  `if.then173.i → if.then176.i`, six links (`colonRefuse_at`). -/
  | colonZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **The comma above depth zero**, on the continuing head: the container pair's four
  sub-routes, eight links each (`commaBraceMerge_at`, `commaBraceRefuse_at`,
  `commaBracketMerge_at`, `commaBracketRefuse_at`).  The type stack's byte at `%sp - 1`
  selects the brace route or the bracket one, the state stack's byte at the same index
  the merge or the refusal. -/
  | commaAboveZero (b1 b2 : UInt8)
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
      (hsp : C.sp ≠ 0)
      (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2) : HcontArm calls G C s
  /-- **The colon above depth zero**, on the continuing head: the marker's three
  sub-routes — the brace pair at eight links (`colonBraceMerge_at`,
  `colonBraceRefuse_at`) and the marker's own refusal at seven (`colonMarkerRefuse_at`).
  A brace marker reads the state stack's byte at `%sp - 1`; any other marker refuses on
  its own byte. -/
  | colonAboveZero (b1 b2 : UInt8)
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
      (hsp : C.sp ≠ 0)
      (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2) : HcontArm calls G C s
  /-- **The container openers `[` and `{` on the continuing head**: both enter
  `if.then.i`, and the four head links beside the tail's five reach the merge — nine
  links (`containerOpenMerge_at`).  The continuing entry's guard is the loop's, not this
  arm's: the merge's index is the push's `C.k + 1`.

  **The call's word is a witness.**  `if.then.i` loads the root slot and hands the word to
  `s2_value_pos`, so `rdv` is the memory's own and not a number the class fixes; the
  staging and the answer are the call's row at it.  The answer `1` is what selects this
  arm — the order is `≤ 519` here and `= 520` at `.openAtCap`. -/
  | containerOpen {b : BitVec 8}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
      (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
      (hsp519 : C.sp ≤ 519)
      {rdv : BitVec 32}
      (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
      (hpreV : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      (r : CallOutcome)
      (hcall : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
      (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) : HcontArm calls G C s
  /-- **A container opener at depth `520`**, on the continuing head: the push's guard
  `ugt %sp.i.0248, 519` is taken at the stacks' staged extent, so the run leaves
  `if.end.i` for `if.then21.i`'s offset store and the copy.  Seven links from the head
  (`containerOpenCap_at`), priced at `7 + 2 ≤ 32` inside one entry's allowance.  The
  depth is the arm's premise: `WalkInv.depth_cap` bounds it by `520` and nothing below
  it, so a state at the extent is a state the invariant admits and the arm must describe.
  The continuing guard is the loop's, not this arm's.  Its word is the call's witness, as
  at `.containerOpen`, and the answer `1` is what selects it.

  **What the arm covers, and what it does not claim.**  It covers every invariant state
  whose `C.sp` is `520` — totality's own requirement, since the census asks for an arm at
  each state the invariant admits.  Document-level reachability is not claimed: the span
  from the seeded head to a depth-`520` head is 520 applications of the opener's step, each
  needing the `s2_value_pos` staging at that state, and neither that iteration nor a `Nat`
  recursion over the walk's depth exists in this tree.  Were depth `520` unreachable from
  the seed, the arm would be vacuous at that premise and harmless — never wrong, only
  unused.  `JsonStage2WalkDispatchOpenersDomain` stages the document that carries the
  bytes and repeats this boundary. -/
  | openAtCap {b : BitVec 8}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
      (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
      (hsp520 : C.sp = 520)
      {rdv : BitVec 32}
      (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
      (hpreV : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      (r : CallOutcome)
      (hcall : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
      (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
      {j : Nat}
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **A container opener whose value-position answer is `0`**, on the continuing head:
  `if.then.i`'s branch is taken, so the run is the head's four pivots, the call, and
  `if.then16.i`'s offset store at `%e + 8` — six links to the refusal copy
  (`containerOpenRefuse_at`), priced at `6 + 2 ≤ 32`.  The *answer* selects this arm, not
  the byte and not the depth: the same two bytes at any depth take it when the callee
  refuses the value, and the same two bytes at a `1` take `.containerOpen` or `.openAtCap`
  instead.  With this constructor the class `91`/`123` is total over the invariant's states
  as well as over the bytes — the answer is always `0` or `1`, and each has its arm.

  **What the arm carries.**  The call's row at its witness word `rdv` — the root slot's
  read, the staging, the outcome and the zero — plus the offset store's three cells.  The
  word is the memory's own: the slot's writers are `entry`'s initial `0` and
  `s2_after_value`'s depth-zero flag `1`, so `0` is not among them and no clause names the
  value.  The arm does not assume the segment it establishes: `containerOpenRefuse_at`
  composes the six links from these cells. -/
  | containerOpenRefuse {b : BitVec 8}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
      (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
      {rdv : BitVec 32}
      (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
      (hpreV : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      (r : CallOutcome)
      (hcall : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
      (hret : r.ret = .int 32 (BitVec.ofNat 32 0))
      {j : Nat}
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **The closing delimiter with a container open**, at the continuing head: `]` and `}`
  at a positive depth, the nesting check's two stack bytes selecting the merge or a
  refusal — `closeWithOpen_at`'s four sub-routes.  The merge keeps the depth and advances
  the index by one; the refusals store the entry's position at `%e + 8`. -/
  | closeWithOpen {v : BitVec 8}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 v))
      (hv : v = BitVec.ofNat 8 93 ∨ v = BitVec.ofNat 8 125)
      (hsp : C.sp ≠ 0)
      {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2)
      (hpreA : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      {j : Nat}
      (hvj : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- **A default-arm letter or high byte**, on the scan-free class: the bytes below `110`
  in the signed order — the letters and the high bytes — whose tag test is clear.  The
  span below `if.else387.i` is `lettersSpan`'s four links (`NodeBlock62`, `LeafBlock54`,
  `if.else405.i`, `if.then413.i`), the kind it leaves is `0`, and the arm's two segments are
  the class's own: the head's chain to `if.else387.i` (its four pivots, `sw.default.i`'s
  succeeding arm, `cond.true345.i`, the bound, the whitespace check and the seam — twelve
  links) and the tail's three calls on their empty arm.  The count is their sum with the
  span and the merge, `12 + 4 + 3 + 1 = 20`, and the composition is
  `lettersCleanupMerge_at`.  The merge's cells come from the segment's endpoint, so nothing
  about the result is supplied.

  **The class is the scan-free one, and the tail's shape says so.**  The tail's three calls
  end at `if.end473.i`, i.e. the copy call's test `ult %ee.1.i %cond350.i` was false, which
  is the token-end class whose byte before the entry's end is not whitespace.  On the run
  class that test is true and the target is `land.rhs457.i`, the scan's landing, so that
  class's segment is the scan's — `HcontFacts`'s, `.ws`'s — and not this one.

  **The chain is counted, and its bound is the longest class's twelve.**  The bytes
  `0 … 43` and `128 … 255` (`.defaultValueLow`) take `NodeBlock5 → LeafBlock →
  sw.default.i`, three pivots, so their chain is **eleven** links
  (`contLowHeadSeg`, `JsonStage2WalkDispatchLettersHead`), while
  `.defaultValueMid`, `.otherValue`, `.defaultValueBracket` and
  `.defaultValueBracketHigh` take four and cost twelve.  The field is therefore the
  class's own count `nH` with `nH ≤ 12`, which is what makes the constructor inhabited at
  every state its class admits; `lettersCleanupMerge_at` takes the same pair. -/
  | letters {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
      (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
      (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
      {Cm : WalkCarry G} {sm : State} {nH : Nat}
      (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
      (hnH : nH ≤ 12)
      (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
      (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
      {Ct : WalkCarry G} {st : State} {tok : Nat}
      (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
        (LetS413 sm x) Ct st 3)
      (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
      (htok : lookupName st.env "%t352.i" = some (.ptr tok)) : HcontArm calls G C s
  /-- **The byte `102` (`'f'`) on the scan-free class**, at the continuing head: the
  letters span's true arm, `LeafBlock54`'s `eq %8, 102` set, so `if.then397.i` (kind `9`)
  rather than `if.else405.i` (kind `0`).  `fSpan`'s four links, with the head's chain to
  the seam (the class's own count `nH ≤ 12`) and the tail's three calls on their empty
  arm: `nH + 4 + 3 + 1 ≤ 20`, and the price `≤ 22 ≤ 32` spends no byte term — the
  tail's endpoint is `if.end473.i`, the copy call's `ult v v` arm. -/
  | fLetter {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
      (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
      (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
      {Cm : WalkCarry G} {sm : State} {nH : Nat}
      (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
      (hnH : nH ≤ 12)
      (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
      (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
      {Ct : WalkCarry G} {st : State} {tok : Nat}
      (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
        (FS413 sm x) Ct st 3)
      (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
      (htok : lookupName st.env "%t352.i" = some (.ptr tok)) : HcontArm calls G C s
  /-- **The class-C span's leaves on the scan-free class**, at the continuing head: the
  bytes `110 … 125` in the signed order — `110` via `LeafBlock56`'s true arm (`110`'s own
  leaf test, kind `10`), `111 … 115` via its else arm, `116` from `LeafBlock58` itself
  (kind `8`) and `117 … 125` via its else arm.  The span is the byte's own
  (`c56TrueSpan`, `c56ElseSpan`, `c58TrueSpan`, `c58ElseSpan`) at `nS ≤ 5`; the head's
  chain to the seam costs the class's own count (`nH ≤ 12`) and the tail's three calls
  end at `if.end473.i` on their empty arm, so `nH + nS + 3 + 1 ≤ 21` and the price
  `≤ 23 ≤ 32` with no byte term.
  The class is `126`/`127`'s complement in `[110, 125]`, and `.ws`/`.cleanup` are theirs. -/
  | classC {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq x (BitVec.ofNat 8 125) = 1)
      {Cm : WalkCarry G} {sm : State} {nH : Nat}
      (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
      (hnH : nH ≤ 12)
      (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
      (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
      {Cs : WalkCarry G} {ss : State} {nS : Nat}
      (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
      (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
      {Ct : WalkCarry G} {st : State} {tok : Nat}
      (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
      (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
      (htok : lookupName st.env "%t352.i" = some (.ptr tok)) : HcontArm calls G C s
  /-- **The default arm's run class**, at the continuing head: the byte before the
  entry's end is whitespace, so the whitespace skip runs, the token's end `%ee.1.i` is the
  run's *stop* `k`, and the copy call's test `ult k v` is true — the extra-token scan is
  entered and the merge follows its exit.  `RunFacts` carries the path's inputs (the head
  chain with the run's count `N`, the byte's span at `nS ≤ 5`, the tail's *scan* arm, the
  landing, the visits' facts and the budget fact) and `runScanMerge_at` composes the
  segment with the merge's three cells at its endpoint, the visits by `scanRoundsAt` — the
  rounds at the seam's own bound, which is what the class-C-only `scanWsRounds` is not.

  **This is the continuing level's class.**  The last entry's run class is priced
  differently: past the last entry the `entryPos` form of the byte credit is zero
  (`entryPos G G.nep = 0`), so a price read through it charges nothing for the document the
  entry has left.  The credit itself is not zero — `boundary G G.nep = G.n` — and
  `WalkDispatchResult.mergeLast` states it at the boundary, so a run there spends the
  entry allowance and the entry's remaining document together.  That class is
  `LastEntryArm.run` beside `RunLastFacts`
  (`JsonStage2WalkDispatchRun`, `JsonStage2WalkDispatchArms`). -/
  | run (f : RunFacts G C s) : HcontArm calls G C s

/-- **The continuing entry's bundle**: the arm at every head state with an entry left.  A
`Type`-valued abbreviation, so the bundle is the arm and not a proposition about it; the
class the arm is read at is `HcontClass`, and the document's byte beside it is the
payload's `HcontByteClass`.  Its producer is
`walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing`), and the loop's step
and `WalkPremises` read it. -/
abbrev WalkContinueFacts {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontArm (stage2Calls stage2SubCalls) G C s

/-- **The dispatch, from the arm.**  Each proved arm runs its own theorem; the standalone
string is `ofStringMerge` at the arm's residue and its depth split, and the positive-depth
opener is the merge or the refusal its route reached.  Every constructor is a proved
class, and the arm is total over `HcontClass.complete`'s bytes *and* over the invariant's
states: `HcontClass.stringOpener` at `C.sp ≠ 0` is
`stringOpenAboveZeroMerge`/`stringOpenAboveZeroRefuse`, and all four states the earlier
split lacked (`}` at zero, an opener at `520`, an opener whose call answers `0`, the
opener above zero) now have one. -/
theorem HcontArm.dispatch {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) :
    HcontArm (stage2Calls stage2SubCalls) G C s →
      WalkDispatchResult (stage2Calls stage2SubCalls) G C s
  | .ws f =>
    (fun ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblk, hkC, hpre, hsp, hspv,
        hkOp, hk2, hnepv, hbelow, _hnep, hadvance, hspcap, hspw, hprice⟩ =>
      WalkDispatchResult.merge Cd sd p spv k2 prev spOp kOp nepv seg hblk hkC hpre hsp hspv
        hkOp hk2 hnepv hadvance (le_of_lt hbelow) hspcap hspw hprice)
      (walkDispatch_at_continue_cells_ws C s hInv hblock hk f)
  | .cleanup f =>
    (fun ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblk, hkC, hpre, hsp, hspv,
        hkOp, hk2, hnepv, hbelow, _hnep, hadvance, hspcap, hspw, hprice⟩ =>
      WalkDispatchResult.merge Cd sd p spv k2 prev spOp kOp nepv seg hblk hkC hpre hsp hspv
        hkOp hk2 hnepv hadvance (le_of_lt hbelow) hspcap hspw hprice)
      (walkDispatch_at_continue_cells C s hInv hblock hk f)
  | .twoEntry f hsp0 R hR8 =>
    WalkDispatchResult.ofStringMerge G C s hblock hInv f hsp0 R hR8
  | .stringOpenAboveZeroMerge h8 hsp hmark hstate hpreV r hcall Cd sd p k2 nepv hseg
      hblockD hkC prev hprev hpreD hincD hnepD hadvance hcap hprice => by
    have hspv : evalOperand sd (.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    cases hprev with
    | inl h =>
      subst h
      exact WalkDispatchResult.merge Cd sd p Cd.sp k2 "if.then330.i"
        (Operand.reg "%sp.i.0248") (Operand.reg "%inc208.i") nepv
        hseg hblockD hkC hpreD (by decide) hspv (by decide) hincD hnepD
        hadvance hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hprice
    | inr h =>
      subst h
      exact WalkDispatchResult.merge Cd sd p Cd.sp k2 "if.else334.i"
        (Operand.reg "%sp.i.0248") (Operand.reg "%inc208.i") nepv
        hseg hblockD hkC hpreD (by decide) hspv (by decide) hincD hnepD
        hadvance hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hprice
  | .stringOpenAboveZeroRefuse h8 hsp hmark hstate hpreV r hcall href =>
    WalkDispatchResult.ofRefuseAt href
  | .scalar f =>
    (fun ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblk, hkC, hpre, hsp, hspv,
        hkOp, hk2, hnepv, hbelow, _hnep, hadvance, hspcap, hspw, hprice⟩ =>
      WalkDispatchResult.merge Cd sd p spv k2 prev spOp kOp nepv seg hblk hkC hpre hsp hspv
        hkOp hk2 hnepv hadvance (le_of_lt hbelow) hspcap hspw hprice)
      (walkDispatch_at_continue_scalar C s hInv hblock hk f)
  | .scalarRun f =>
    walkDispatch_at_continue_scalarWs hInv hblock hk f
  | .closeBracketZero h8 hsp hv he hj hj64 =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (bracketRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
        (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .closeBraceZero h8 hsp hv he hj hj64 =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (closeBraceZero_at G C s hInv hblock h8 hsp hv he hj hj64
        (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .commaZero h8 hsp hv he hj hj64 =>
    WalkDispatchResult.ofRefuseAt (commaRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
      (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .colonZero h8 hsp hv he hj hj64 =>
    WalkDispatchResult.ofRefuseAt (colonRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
      (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .commaAboveZero b1 b2 h8 hsp hmark hstate => by
    by_cases hb1 : colonBit b1 = 1
    · have hmark1 : C.tyMap (C.sp - 1) = 1 := by
        rw [hmark]; exact uint8_eq_one_of_colonBit hb1
      by_cases hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1
      · exact commaBraceMerge_at G C s hInv hblock h8 hsp hmark1 hstate hb2
      · exact commaBraceRefuse_at G C s hInv hblock h8 hsp hmark1 hstate
          (bitZeroOfNeOne hb2)
    · have hbit : pairBit (BitVec.ofNat 8 b1.toNat) = 0 := by
        simpa only [pairBit, colonBit] using bitZeroOfNeOne hb1
      by_cases hb2 : colonBit b2 = 1
      · exact commaBracketMerge_at G C s hInv hblock h8 hsp hmark hstate hbit hb2
      · exact commaBracketRefuse_at G C s hInv hblock h8 hsp hmark hstate hbit
          (bitZeroOfNeOne hb2)
  | .colonAboveZero b1 b2 h8 hsp hmark hstate => by
    by_cases hb1 : colonBit b1 = 1
    · by_cases hb2 : colonBit b2 = 1
      · exact colonBraceMerge_at G C s hInv hblock h8 hsp hmark hstate hb1 hb2
      · exact colonBraceRefuse_at G C s hInv hblock h8 hsp hmark hstate hb1
          (bitZeroOfNeOne hb2)
    · exact colonMarkerRefuse_at G C s hInv hblock h8 hsp hmark (bitZeroOfNeOne hb1)
  | .containerOpen h8 hopen hsp519 hread hpreV r hcall hret =>
    containerOpenMerge_at G C s hInv hblock h8 hopen hsp519 hread hpreV r hcall hret
  | .openAtCap h8 hopen hsp520 hread hpreV r hcall hret hv he hj hj64 =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (containerOpenCap_at G C s hInv hblock h8 hopen hsp520 hread hpreV r hcall hret
        hv he hj hj64)
  | .containerOpenRefuse h8 hopen hread hpreV r hcall hret hv he hj hj64 =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (containerOpenRefuse_at G C s hInv hblock h8 hopen hread hpreV r hcall hret
        hv he hj hj64)
  | .closeWithOpen h8 hv hsp hmark hstate hpreA hvj he hj hj64 =>
    closeWithOpen_at G C s hInv hblock h8 hv hsp hmark hstate hpreA hvj he hj hj64
  | .letters h8 hbit h110 hne102 hHead hnH hm hmk h8m hTail ht htk htok => by
    obtain ⟨Cd, sd, p, hseg, hblockD, hkD, hpreD, hincD, hnepD, hpriceD⟩ :=
      lettersCleanupMerge_at G C s hInv hblock h8 hbit h110 hne102 hHead hm hmk h8m
        hTail ht htk htok hnH (by omega)
    have hspv : evalOperand sd (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge Cd sd p Cd.sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hpriceD
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD
  | .fLetter h8 hbit h110 h102 hHead hnH hm hmk h8m hTail ht htk htok => by
    obtain ⟨Cd, sd, p, hseg, hblockD, hkD, hpreD, hincD, hnepD, hpriceD⟩ :=
      fCleanupMerge_at G C s hInv hblock h8 hbit h110 h102 hHead hm hmk h8m
        hTail ht htk htok hnH (by omega)
    have hspv : evalOperand sd (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge Cd sd p Cd.sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hpriceD
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD
  | .classC h8 h110 h125 hHead hnH hm hmk h8m hSpan hs hnS hTail ht htk htok => by
    obtain ⟨Cd, sd, p, hseg, hblockD, hkD, hpreD, hincD, hnepD, hpriceD⟩ :=
      classCMerge_at G C s hInv hblock h8 h110 h125 hHead hm hmk h8m hSpan hs hnS
        hTail ht htk htok hnH (by omega)
    have hspv : evalOperand sd (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge Cd sd p Cd.sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hpriceD
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD
  | .run f => by
    obtain ⟨Cm, sm, nSc, hseg, hInvD, hblockD, hpreD, hkD, hincD, hnepD, _hnR, hprice⟩ :=
      runScanMerge_at G C s hInv hblock hk f
    have hspv : evalOperand (revMergeS sm f.c) (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 (revMergeC Cm).sp)) := hInvD.depth_reg
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge (revMergeC Cm) (revMergeS sm f.c)
      (f.nH + f.nS + 8 + nSc) (revMergeC Cm).sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hInvD.depth_cap hInvD.sp_le_wlen hprice
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.HcontClass.complete
#print axioms LeanLLVM.Refinement.WalkScope.HcontClass.value_of_48
#print axioms LeanLLVM.Refinement.WalkScope.HcontArm.dispatch

end WalkScope
end LeanLLVM.Refinement
