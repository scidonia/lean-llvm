/-
The continuing entry's dispatch: one arm per head-switch class, and the census.

## What was wrong

`WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) asked for `HcontCase` at every
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
* `.scalar` — **`HcontScalarFacts`**, the plain-value class on the numeral route: the
  head's four scalar pivots, the count test's succeeding arm, the no-run byte class and
  the tag test's true arm, composed through `walkRevolutionMergeSegScalar`
  (`JsonStage2WalkHcontScalar`).  This is the class the old split excluded, and it is
  proved — not supplied — so the document `"01"`'s head is a merge arm.
* `.closeBracketZero` — `if.then53.i` at depth zero on the **continuing** head: `]` with
  nothing open is refused (`bracketRefuse_at`'s chain; its only count premise is the head's
  guard, which a continuing entry has).  This is the one refusal arm the continuing side
  shares with the last entry's, and it is proved rather than supplied.
* `.supplied` — the arms whose segments are the remaining obligation: the comma, the
  colon, the container openers, the closing brace and the close bracket with a container
  open, and the default arm's letter and high-byte routes.  The field is that arm's own
  counted segment to the endpoint it reaches, with the endpoint's facts — not a bundle
  about another class.

Each constructor carries only its own arm's premises, and the price is the dispatch's own
(`WalkDispatchResult`'s), so no class's byte restriction is a premise of another's.

## Why the token-end class is not part of the census

The head switch's tests are on the entry's first byte (`%8`), and the tag test is the same
byte's.  The whitespace run is decided by the byte before the *entry's end* (`%35`), which
is the document's content rather than the head state's dispatch; so it is each one-entry
arm's own premise (`HcontFacts.hClass`, `HcontCleanupFacts`'s three no-run bits,
`HcontScalarFacts`'s three), not a second classification over `%8`.  The two are different
questions, and this module keeps them apart exactly as `JsonStage2WalkDispatchArms` keeps
the last entry's guard apart from its head switch.
-/
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
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
two values split it.  The other arms' tag values are not needed: they take the same
evidence branch (`supplied`) whichever value the bit has. -/
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
  /-- **The standalone string, with its residue and its accepting-arm selector.**
  `R` is the two words the walk layer does not carry, and `hR8` is `NodeBlock31`'s
  test: the model's form is `1` or `2` on the accepting arms, and neither is `< 1`
  signed.  A refusing answer is a legal answer to the same call, so this is the
  arm's premise rather than the state's. -/
  | twoEntry (f : HstringFacts G C s) (R : HstringResidue G C s f)
      (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0) : HcontArm calls G C s
  /-- **The plain-value token on the numeral route** (`HcontScalarFacts`): the class the
  old split excluded. -/
  | scalar (f : HcontScalarFacts G C s) : HcontArm calls G C s
  /-- **A closing bracket at depth zero, with nothing open**: refused at `if.then56.i`.
  The links are `JsonStage2WalkDispatchArms`'s `.closingZero` chain, and its only count
  premise is the head's guard, which a continuing entry has. -/
  | closeBracketZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : HcontArm calls G C s
  /-- The arms whose segment is the remaining obligation: the comma, the colon, the
  container openers, the closing delimiters and the default arm's letter and high-byte
  routes.  The field is that arm's own result — the endpoint it reaches with the count and
  the price — and no other arm's class is a premise of it. -/
  | supplied (r : WalkDispatchResult calls G C s) : HcontArm calls G C s

/-- **The dispatch, from the arm.**  Each proved arm runs its own theorem; the standalone
string is `ofStringMerge` at the arm's residue; the supplied arm is its own result,
carried. -/
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
  | .twoEntry f R hR8 => WalkDispatchResult.ofStringMerge G C s hblock hInv f R hR8
  | .scalar f =>
    (fun ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblk, hkC, hpre, hsp, hspv,
        hkOp, hk2, hnepv, hbelow, _hnep, hadvance, hspcap, hspw, hprice⟩ =>
      WalkDispatchResult.merge Cd sd p spv k2 prev spOp kOp nepv seg hblk hkC hpre hsp hspv
        hkOp hk2 hnepv hadvance (le_of_lt hbelow) hspcap hspw hprice)
      (walkDispatch_at_continue_scalar C s hInv hblock hk f)
  | .closeBracketZero h8 hsp hv he hj hj64 =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (bracketRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
        (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .supplied r => r

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.HcontClass.complete
#print axioms LeanLLVM.Refinement.WalkScope.HcontClass.value_of_48
#print axioms LeanLLVM.Refinement.WalkScope.HcontArm.dispatch

end WalkScope
end LeanLLVM.Refinement
