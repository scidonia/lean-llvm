/-
`s2_string_body`'s emitted body: the AST it parses to, its ten blocks pinned and
run, the expander's clause at the call's own arguments, and the contract proved of
the body — `s2StringBodyBody_contract`, at `s2StringBodyBudget`'s fuel.

`JsonStage2HelperIR` pins `s2_string_body`'s text only as far as its parse.  This
module takes the same step the sibling rows' bodies took, and has taken it this
far: the ten blocks are transcribed and `#guard`ed against the fixture; each block
is a `denoteCode` run and a control step, with its branch bit named; the scan is a
`BoundLoop` value at `cost = 2` whose invariant is seated at the head the entry
leaves; and every path -- the body-itself arm, the decoded length, the refusal
record, through `land.lhs.true`'s inside test or straight out of the scan -- has
its terminal run proved.  The memory primitives the closing rests on are proved
too: writing a region twice is the second write, a region the memory holds is
written back in place, and two in-place writes over disjoint regions commute once
the commutation lemma's two swaps are in.

**The closing** composes them: `s2StringBodyBody_contract` seats the scan at the
head the entry leaves, runs it from the budget it was seated with, and dispatches
over the four arms the exit admits — the body-itself form, the inside test's
decoded answer and its refusal record, and the scan's own straight exit — each
ending at a terminal run whose memory is the callee's own arm.  The post and the
frame therefore come from the arm, and the fuel from `s2StringBodyBudget`.

**The closing's one statement-level finding, and the only one here that was false
rather than under-specified**: `if.end` compares the expander's return against the
sentinel `0xffffffffffffffff` and takes the refusal path when it matches, while the
model's `stage2StringBody` has no sentinel branch.  At a decoded answer of exactly
`2 ^ 64 - 1` bytes the body answers form 0 and the model form 2, so no
postcondition holds at that input; `s2StringBodyPre`'s `len.toNat + 1 < 2 ^ 64`
excludes that one document length — sixteen exabytes — and the staging's own
docstring states why.  One more fact of the chain's shape belongs to the closing:
`BoundLoop.cost` is a structure projection, so a bound the loop hands back mentions
it opaquely and `omega` needs it stated at the numeral.

**The file's order is the dependency's**: the fixtures and the pinned AST, then
the block pins (`findBlock`, instruction lists), then the one-instruction steps,
then the runs — a run placed before a step it calls reads as an unknown
identifier.  **The chain's four facts**, each of which cost a revert to find: a
step is applied at the **cons** environment the previous step built (the named
`Env` definitions are the statement's spelling, reconciled at the end); the
allocator cell is `(Ty.int 64).sizeBytes`, not the numeral it reduces to; a
one-cell-deep lookup is `(by s2_lk)`; and `denoteCode_load64`'s implicit value
must be named (`(v := …)`) or its metavariable survives into the closing goal.

**And the fourth**: a statement whose environment or memory nests more than three
deep gets a `def` — there the parser's layout, not the prover, decides whether the
lemma exists at all.

**A fact two sections share belongs before both.**  The order above (fixtures,
steps, runs) is a dependency order and says nothing about a lemma that one
section states and another consumes; `readBytes_length_some` was written in the
bits section and read by the memory section, and had to move.  Stating such a fact
ahead of both is the rule, not an afterthought.

**And the fifth**: every term a chain matches on is the *unreduced* form the
emitting step produces, so the statement's `def` and the chain's patterns must be
written from the produced term and not from the source text.  Three parts, each
measured on `if.then11`: a `getelementptr`'s address is `a + n.toNat` with the
literal's `toNat` unreduced (`c + (1112#64).toNat`, not `c + 1112`); a stored
value likewise (`natToBytes (0#32).toNat 4`, not `natToBytes 0 4`); and an
arithmetic cell is `x + c` in the immediate's own `BitVec` form.  The two sides of
a failed reconciliation are printed by the compiler, which is where the produced
term should be copied from — and **two margins**: the final reconciliation must
rewrite *both* `denoteCode []` occurrences (`simp only [denoteCode_nil, …]`, not a
single `rw`), and a step's `_` slot can hide a **bound** as easily as a value, so
when the two sides print identically and the goal will not close, the residual is
a side condition of a step rather than a mismatch of terms.

**And the two vocabulary gaps this module had to fill.**  `Lexis`-level facts the
cone does not carry: `Memory` proves the *below* case for a sequence read
(`readBytes_writeBytes_below`) and only the single-byte case above it, so
`s2StringBodyReadBytes_above` is proved here — a four-byte lane read past a write
needs it.  And there is no `getElem?_isSome`: `ps[c]? = some q` yields `c <
ps.length` through `List.getElem?_eq_none` and `cases` on the resulting absurdity.
`readLanes32_nth` states what `readLanes32_lane` states here and lives in the
walk's cone, out of this module's imports; the two names differ deliberately, so a
consumer importing both has one of each rather than an ambiguity.

**The body.**  `entry` converts the two addresses and reads the cursor word;
`land.rhs`/`while.body` scan the position list forward to the body's first
position; `land.lhs.true` tests whether that position is inside the body;
`if.then` is the body-itself form; `if.end` calls the expander; `if.then11` writes
the refusal record and `if.end14` the decoded length; `cleanup` and `cleanup16`
select the returned form.  `%ei` is the body's own eight-byte slot for the
expander's offset, which is why the block opens with an `alloca`: it is one of the
four body-allocated objects no caller stages.
-/

/-
This module is the interface its consumers import: the body proof is in the
modules below, in dependency order, and the imports re-export every name.
-/
import LeanLLVM.Refinement.JsonStage2StringBodyAST
import LeanLLVM.Refinement.JsonStage2StringBodyFootprints
import LeanLLVM.Refinement.JsonStage2StringBodyMemory
import LeanLLVM.Refinement.JsonStage2StringBodyBlocks
import LeanLLVM.Refinement.JsonStage2StringBodyArms
import LeanLLVM.Refinement.JsonStage2StringBodyJoin
import LeanLLVM.Refinement.JsonStage2StringBodyDecoded
