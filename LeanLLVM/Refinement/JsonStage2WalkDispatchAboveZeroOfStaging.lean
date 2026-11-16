/-
# The comma's continuing arm, from the staging

`HcontArm.commaAboveZero` (`JsonStage2WalkDispatchHcontArms`) is the continuing entry's
comma at a positive depth: the head switch's `if.then127.i` and the container pair's four
sub-routes — the type stack's byte at `%sp - 1` selecting the brace route or the bracket
one, the state stack's byte at the same index the merge or the refusal — eight links each
(`commaBraceMerge_at`, `commaBraceRefuse_at`, `commaBracketMerge_at`,
`commaBracketRefuse_at`).  This module produces the arm's evidence at every state that
carries the invariant, which is the state family the loop's step quantifies over, and
composes it into the dispatch.  The only form the arm existed in was the document-level one
(`commaAboveZero_cont_at_document`), whose statement carried the two stack bytes as
premises because the depth-one reachability theorem does not expose the reached carry's
maps; the producer takes the state's own carry instead, so those premises are gone.

## The arm's residual rows, as the enumeration marks them

`JsonStage2WalkTerminalPrice`'s section 2 lists this arm as **D** `h8` = 44; **D**
`hmark`/`hstate` (witnesses `C.tyMap (C.sp - 1)`, `C.stMap (C.sp - 1)`); **F-split**
`C.sp ≠ 0`, with no (ii) calls and no (iii) traversal.  It is the cheapest row of the
enumeration: six binders, of which two are the witnesses for the two stack maps, so four
statements — the byte, the depth and the two stack cells — of which one is supplied and
three are derived.  The zero-depth refusals beside it have the same single free premise but
five derived cells, including the entry's position and its two document bounds; they are
produced in `JsonStage2WalkDispatchZeroOfStaging`, where `entryPos_le` and `entryPos_lt_64`
are the two bounds.  Producing this arm confirms all three marks:

| row | mark | how the producer has it |
|---|---|---|
| `h8` | **D** | `WalkInv.iter.reg8` is the `%8` cell at every state and `hlastByte G C` is its witness (`cont_reg8`); the class's byte test then pins the value (`eq_bit_value`).  Nothing about the document is supplied beyond the class |
| `hmark` | **D** | the witness `b1 := C.tyMap (C.sp - 1)`, so the field is `rfl` |
| `hstate` | **D** | the witness `b2 := C.stMap (C.sp - 1)`, `rfl`, as `hmark` |
| `C.sp ≠ 0` | **F-split** | a named premise.  `WalkInv.depth_cap` bounds the depth above only (`C.sp ≤ stage2StackExtent`, which is 520), and a head state at `C.sp = 0` carries the same invariant, so zero-versus-positive is the document's rather than the state's |

Two premises in — the class's byte test and the depth split — and the arm out.  The two
stack rows are the cheap kind of **D**: they are not functions of the class, the registers
or the geometry, but of the carry's own two maps, which the witness choice reads directly.
No clause of `WalkInv` is consulted for them, and a producer that took them as premises
would supply data the state already holds.  That is the whole of the arm's residual: the
class demotion and one depth selector.

## What the class demotion costs the remaining arms

`eq_bit_value` is stated at an arbitrary byte `x` and an arbitrary byte literal `c`, so
every arm whose census class is a byte equality takes it unchanged: `.stringOpener` (34),
the comma's two (44), the colon's two (58) and `.closeBracketZero` (93) at the literal, and
the two arms whose class is one of two literals — `.closeWithOpen` (93 or 125) and
`.containerOpen` (91 or 123) — which fill their disjunction from the pinned byte.  What it
does **not** do is settle an arm whose byte is not a literal.  The default arm's three spans
take the head's byte as a field `x` (`.letters`, `.classC`) or beside an equality bit
(`.fLetter`'s `· = 102`), so their `h8` is `some (.int 8 x)` and the demotion is not what
they need; the census separates their bytes by ranges, which no single equality test names.
The high-byte bundles are the same shape for a different reason: `126` and `127` are one
class of two bytes, so `HcontFacts` and `HcontCleanupFacts` carry the byte as a field `x`
and take `hlt125`/`hne125` as premises rather than deriving a value.

So the demotion generalises, and it is not where the remaining arms cost lives: what a
still-unproduced arm needs beyond it is what its own row names — the openers' and the
closing delimiter's callee preconditions and answers, and the default arm's counted head
chain and three-call tail, which are segments a producer must have before its span can be
composed.  This module's arm needs none of them, which is why the enumeration marks it
first.  The zero-depth refusals' `entryPos`/`%e` cells and their two document bounds, which
this paragraph used to list here, are produced beside this one
(`JsonStage2WalkDispatchZeroOfStaging`): `WalkInv.idx_reg` and `WalkInv.regs` are the two
cells, and the geometry bounds `entryPos` at every index, so the class and the depth split
are all a wrapper supplies.

## The colon, at both levels

The comma's twin is the same arm at the marker's own entry (`if.then173.i`), and its
constructor is the same four statements: the byte, the positive depth and the two stack
cells.  Its two levels are produced here as the comma's continuing level is —
`hcontArm_colonAboveZero_of_staging` and `lastEntryArm_colonAboveZero_of_staging` — so the
document wrappers at `[:`/`{:` and `[:0` no longer name the reached carry's two maps: the
`…Domain` module's implication premises `C'.tyMap (C'.sp - 1) = … → C'.stMap (C'.sp - 1) =
… →` are gone with them.  The last entry's producer takes the level's negated count
(`¬ (C'.k + 1 < G.nep)`) rather than the dispatch's, because the dispatch is where the
split is decided; the arm itself carries nothing beside the class and the depth.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The two cells the arm reads -/

/-- **`%8`'s word is the head byte.**  `WalkInv.iter.reg8` read as an operand: the cell is
`hlastByte G C` at every state that carries the invariant, and every continuing arm takes
its byte premise in this shape. -/
theorem cont_reg8 {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C)) := by
  simp only [evalOperand]
  exact hInv.iter.reg8

/-- **A byte-equality test pins its value.**  The census's `eq` arms — `HcontClass`'s
`stringOpener` (34), the comma's and the colon's byte tests, the bracket's and the brace's,
and the tag test's `45` — read a one-bit equality, so a set bit *is* the equality of the two
bytes.  It is stated at an arbitrary `x` and literal rather than at `hlastByte G C`, because
it is the demotion every `eq`-classified class shares. -/
theorem eq_bit_value {x : BitVec 8} {c : Nat}
    (h : evalICmp .eq x (BitVec.ofNat 8 c) = 1) : x = BitVec.ofNat 8 c := by
  by_contra hne
  have h0 : evalICmp .eq x (BitVec.ofNat 8 c) = 0 := by
    simp [evalICmp, hne]
  rw [h0] at h
  exact absurd h (by decide)

/-- **The class test, from the `%8` cell.**  `cont_reg8`'s inverse direction: a state whose
`%8` holds the literal `x` has the census's byte test set at `x`, because the head byte
*is* that literal (`WalkInv.iter.reg8` names it, and the two readings are one value).  A
producer takes the class as its premise, so this is what a wrapper holding the cell — a
reachability theorem's own endpoint, or a document's byte — composes it with. -/
theorem hclass_of_reg8 {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {x : BitVec 8}
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    evalICmp .eq (hlastByte G C) x = 1 := by
  have hval : hlastByte G C = x := by
    have h1 : lookupName s.env "%8" = some (.int 8 x) := by
      simpa only [evalOperand] using h8
    have h := Option.some.inj (hInv.iter.reg8.symm.trans h1)
    simpa using h
  rw [hval]
  exact walkEvalICmp_eq_self _

/-! ### The arm, and the dispatch it feeds -/

/-- **The comma's continuing arm, from the staging.**  `HcontArm.commaAboveZero` at every
state that carries the invariant, a positive depth and the comma's byte: the byte is the
invariant's `%8` cell at the class's own value, and the two stack bytes are the carry's
maps at `%sp - 1` — a projection, not a premise.

The class premise is the census's byte test at the head byte, which is what a dispatcher
holding `HcontClass.comma h44 heq` has in hand (`heq` here); `h44` is the same
constructor's other bit and is not read, because the equality already fixes the value. -/
def hcontArm_commaAboveZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1)
    (hsp : C.sp ≠ 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .commaAboveZero (C.tyMap (C.sp - 1)) (C.stMap (C.sp - 1))
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp rfl rfl

/-- **The comma's continuing dispatch, from the staging.**  The arm above through
`HcontArm.dispatch`, whose four sub-routes are selected by the two stack bytes the producer
read off the carry: the outcome is the state's, and no sub-route's premise is supplied. -/
theorem walkDispatch_at_commaAboveZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1)
    (hsp : C.sp ≠ 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk (hcontArm_commaAboveZero_of_staging C s hInv hclass hsp)

/-! ### The colon, at both levels

The comma's twin: the same four statements at `if.then173.i`, and the same two projections
for the stack cells.  The only difference between the two levels is the count the
dispatch states, so each producer is the comma's with the lane's literal and each
dispatch is its own level's. -/

/-- **The colon's continuing arm, from the staging.**  `HcontArm.colonAboveZero` at every
state that carries the invariant, a positive depth and the colon's byte.  The marker's
three sub-routes (the brace pair and the marker's own refusal) are selected by the two
stack bytes the witness reads off the carry, so no sub-route's premise is supplied. -/
def hcontArm_colonAboveZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp ≠ 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .colonAboveZero (C.tyMap (C.sp - 1)) (C.stMap (C.sp - 1))
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp rfl rfl

/-- **The colon's arm at the last entry, from the staging.**  The same four statements at
the level whose count is exhausted; which side of the count the state is on is the
dispatch's hypothesis, so the arm is the continuing one's term. -/
def lastEntryArm_colonAboveZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp ≠ 0) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .colonAboveZero (C.tyMap (C.sp - 1)) (C.stMap (C.sp - 1))
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp rfl rfl

/-- **The colon's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_colonAboveZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp ≠ 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk (hcontArm_colonAboveZero_of_staging C s hInv hclass hsp)

/-- **The colon's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_colonAboveZero_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp ≠ 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_colonAboveZero_of_staging C s hInv hclass hsp)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cont_reg8
#print axioms LeanLLVM.Refinement.WalkScope.eq_bit_value
#print axioms LeanLLVM.Refinement.WalkScope.hclass_of_reg8
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_commaAboveZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_commaAboveZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_colonAboveZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_colonAboveZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_colonAboveZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_colonAboveZero_last_of_staging

end WalkScope
end LeanLLVM.Refinement
