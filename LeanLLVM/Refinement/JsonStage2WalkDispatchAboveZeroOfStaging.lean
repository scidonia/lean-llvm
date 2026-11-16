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
five derived cells, including the entry's position and its two document bounds.  Producing
this arm confirms all three marks:

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
still-unproduced arm needs beyond it is what its own row names — the zero-depth refusals'
`entryPos`/`%e` cells and their two document bounds (`hj`, `hj64`), the openers' and the
closing delimiter's callee preconditions and answers, and the default arm's counted head
chain and three-call tail, which are segments a producer must have before its span can be
composed.  This module's arm needs none of them, which is why the enumeration marks it
first.
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

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cont_reg8
#print axioms LeanLLVM.Refinement.WalkScope.eq_bit_value
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_commaAboveZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_commaAboveZero_of_staging

end WalkScope
end LeanLLVM.Refinement
