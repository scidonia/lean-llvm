/-
# The dispatch's residual rows, and the classes that need none

`WalkContinueFacts` and `WalkLoopEnd` (`JsonStage2WalkPremisesOfStaging`) are the loop's
two supplies: the continuing entry's arm at every invariant head with an entry left, and
the last entry's arm at every invariant head without one.  Neither is a theorem of this
tree.  This module states why, per class, and produces the part that is:

* at the classes whose rows the layer **derives**, the arm is a theorem at every state
  that carries the invariant — `hcontArm_of_derivedClass` and
  `lastEntryArm_of_derivedClass`, through `HcontArm.dispatch` and `LastEntryArm.dispatch`;
* at the remaining classes the arm's payload is a row that no clause of `WalkInv` supplies,
  and the table below names which row, and from which producer;
* the terminal price row is not a supplied value at all: at the document `"abcdefgh "` the
  entry allowance's form of it is false (`runLast_budget_false_at_eight`), which is what
  `JsonStage2WalkTerminalPrice`'s credit form pays and the entry-only spelling does not.

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

## The two states that had no arm, and the arms that supply them

The census this module recorded had two holes: two head states the switch sends to a
refusal no constructor's class admitted, so `WalkContinueFacts` and `WalkLoopEnd` could not
be total at them.  Each is now an arm of its own, at both levels, with its own producer and
price — and both are the delimitation boundary's, which is where the lengths are:

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
  priced at `7 + 2 ≤ 32`, with the value-position call's staging, the root slot's zero word
  and the call's answer `1` carried exactly as `.containerOpen` carries them and `C.sp =
  520` in place of `C.sp ≤ 519`.

Both states are one byte or one nesting away from an ordinary document, so neither is
excluded by the input domain: `"}"` and 520 nested `[` are admitted, malformed and
deeply-nested inputs.  That is why the arms were owed rather than the domain narrowed.

With them the *census* is total: every state the invariant admits is in some constructor's
class at its level — the class is the byte, the depth's zero/positive split, and the
token-end class, and `.closeBraceZero` and `.openAtCap` fill the two depth cases the split
had no arm for.  What remains supplied per class is the arm's *payload*, the table below's
rows, not a state left outside the enum.

## The rows the remaining classes take, and from which producer

The class is the arm's own, so no row here is another arm's class.  **ABI** is a callee's
precondition or answer at the arm's argument list; **document** is the input's content read
as a value; **traversal** is the scan's round, guard and byte facts.

| level | class | producer | row that stops the derivation | kind |
|---|---|---|---|---|
| both | `.ws` (`126`/`127`, entry left) | `hcontFacts_of_staging` | `hlt125`/`hne125`; the stop's budget conjunct; `hTail`'s three calls | document, ABI |
| both | `.cleanup` (`126`/`127`, last entry) | `hcontCleanupFacts_of_staging` | the class's bits and `hb13`/`hb32`/`hbne13` from the last byte; `hTail` | document, ABI |
| both | `.twoEntry` (`"`, entry left) | `hstringFacts_of_staging` | `s2_string_body`'s staging: the allocator cursor's placement, the log's arena word, the byte spacing, the escape count's sign bound; the next lane | ABI, document |
| both | `.scalar` | `hcontScalarFacts_of_staging`, `lastEntryArm_scalar_of_staging` | the root word's zero; the last byte's class; the three calls — their preconditions and answers at the returned memories | document, ABI |
| last | `.highByte` (`126`/`127`) | `hlastFacts_of_staging` | `HlastResidue`: the head bits, the last byte's class, the root word, the three calls | document, ABI |
| both | `.containerOpen` (`[`, `{`) | `containerOpenMerge_at` | the `519` boundary (above); the root word's zero; `s2_value_pos`'s outcome and the `1` its contract gives | document, ABI |
| both | `.letters`, `.fLetter` | `hcontArm_letters_of_staging`, `hcontArm_fLetter_of_staging` | `hTail`: the tail's three calls | ABI |
| both | `.classC` (`110 … 125`) | `hcontArm_classC_of_staging` | `hTail`; the byte's own span | ABI |
| both | `.run` | `runFacts_of_staging`, `runLastFacts_of_staging` | the traversal (`hbyte`); the tail's scan arm; the landing; the scan's counter and bound; the lane's order; the price | traversal, document |

The head chains and the spans are **derived in principle** — the segment lemmas
(`hlastTailSeg`'s eleven links, `walkHeadChainCSeg`, `hlastPrefixSeg`) compose them from
the class's bits and the endpoint cells — but no lemma exposes one as a segment apart from
the tail's three calls, so the producers take them beside `hTail`.  Retiring them moves
work, not closure: `hTail` remains, and it is the row that blocks the spans.

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

`RunLastFacts.hbudget` is `N + 4 * (c - 1 - i) ≤ 6` — the entry allowance's form of
`terminalPriceFits`.  At `"abcdefgh "` the terminal run is eight links, so the form is
false at the document's own numbers, and a producer that took `N`, `c` and `i` from the
document could not state it.  `JsonStage2WalkTerminalPrice`'s credit form pays the same
document (`6 + 8 * (n - ix)`); restating `mergeLast`'s price at the boundary is what would
supply the row, and that is a change to the dispatch's statement rather than a proof of
this one.
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

/-- **The terminal price's entry-only form is false at `"abcdefgh "`.**  The run class's
price row is `N + 4 * (c - 1 - i) ≤ 6` at the state's numbers, and `RunLastFacts` carries
the ties that name them — the stop inside the document, the document's length, the run
beginning at the entry's position.  At eight continuing bytes in one entry the terminal run
is eight links, so the row is false at the numbers a producer of that class supplies: the
row cannot be derived from the document, and a producer that took its values from the
document could not state it.  `JsonStage2WalkTerminalPrice`'s credit form pays the same
document; the entry allowance's form does not. -/
theorem runLast_budget_false_at_eight {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
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
#print axioms LeanLLVM.Refinement.WalkScope.runLast_budget_false_at_eight

end WalkScope
end LeanLLVM.Refinement
