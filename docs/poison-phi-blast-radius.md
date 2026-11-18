# The poison-phi change: its blast radius, and what would bound the next one

**Date:** 2026-11-18. **Revision at report:** the change is in flight at `b7682bb`; the semantics half is green, four downstream modules are red.

## The change

`Value.poison` is added as a distinguished value. `phiSelect` binds it for a selected poison incoming instead of failing; `evalOperand` refuses it at the read, so the marker is observable only through a use. `Const.toValue .poison = none` is kept: a poison *immediate operand* read directly is a use and stays `.ub`.

The intended blast radius was: `evalOperand`, plus any consumer that reads a cell without it.

## How it actually rippled

| layer | what happened |
|---|---|
| `Basic.lean`, `Semantics.lean`, `BlockEval.lean` | core: constructor, `phiSelect`, `evalOperand`, `Value.intToNat .poison = none`, `evalOperand_ne_poison`, `evalOperand_reg_of` (autoParam side condition, so ~600 call sites are unchanged), `step_ret_ne_poison`/`runFuel_ret_ne_poison`. Green. |
| `CommaMaskIR` | the `or_reg`/`select` lemmas' **statements** had to change: a poisoned operand is a use, so the right-hand side is stated over `evalOperand`. Proofs rewritten, `simp` users updated. Green. |
| `ConstantFold` | `substOperand` now refuses to replace a register by `poison`, so the pass cannot turn a failing selection into a marker. Substitution lemmas re-proved. Green. |
| `SeamContext` | callee returns are never the marker. Green. |
| `CommaMaskLoop` | 5 missing poison arms, 6 type mismatches from the restated lemmas, 3 unsolved. Red. |
| `JsonEntrySteps` | 10 unsolved in `ent_auto` steps. Red. |
| `JsonEscapeBatch` | 1 unsolved, plus 13 `#guard_msgs` axiom docstrings to re-record. Red. |
| `DepthCountRefine` | 1 unsolved. Red. |
| `Relation`, `StrengthReduce`, `ITree/Interpret`, `ITree/Bridge`, `JsonEntrySteps`/`JsonEscapeBatch`/tests copies | edited, unverified. |
| `JsonStage2NumFastTier3` | the restatement is written, uncompiled. |

## Why it was bigger than estimated

The estimate was about *phi selection*. The actual change is about **the meaning of value-reading**: once a poison value can be in a cell, every lemma stated in terms of `evalOperand` needs re-checking, because "the value in this register" is now a partial fact, not a total one. The `or_reg`/`select` lemmas were the visible case, and they were unavoidable — a poisoned operand is a use, so the statement must be about `evalOperand` rather than about a value.

So the blast radius is not "phi selection plus `evalOperand`"; it is **every lemma whose statement mentions `evalOperand`, `evalOperands`, or `Const.toValue`**, plus the proofs that consume them.

## What would bound the next one

1. **Enumerate the value-reading surface *before* editing.** `grep` for every lemma whose statement mentions `evalOperand`, `evalOperands`, or `Const.toValue`, and for every `Value` pattern match. That list *is* the blast radius, and it can be produced before the first edit instead of discovered by the build.

2. **Prefer an autoParam side condition for a semantics addition.** `evalOperand_reg_of`'s side condition left ~600 call sites unchanged, because the consumer's statement gains a hypothesis rather than changing shape. That is the cheapest form of a widening, and it should be the default for a new value constructor.

3. **Assert the intended behaviour first, at the smallest synthetic body.** The two-successor regression — one successor reads the cell (must be `.ub`), one does not (must jump) — is written before the fallout is fixed, so a wrong shape fails fast and cannot be mistaken for a faithful one.

4. **Land core, then lemmas, then dependents, in that order.** The red subtree is bounded by the import graph: `LeanLLVM.lean` should import new modules only once the core and the restated lemmas are green, so the root is not red while they are being repaired.

5. **Replace, never weaken.** The lemmas the change makes false are replaced with the read-conditional form *and* a positive statement at the same block (the residual block's own step is a jump). A lemma that is false under a change must not be kept with a side condition: that is how a vacuous statement survives in a build log.

6. **Keep the patch discipline.** Every round that stops saves a patch before restoring, so a red subtree costs elapsed time and not work.

7. **Read the axiom pins after each module.** A proof that quietly gains a carrier is invisible in a diff; `#print axioms` after each module is how it is caught.

## What went right

The autoParam side condition kept ~600 call sites unchanged. The regression distinguishes a faithful change from a weakening. The false lemmas are being replaced rather than preserved with a condition. And the work is preserved at every stop, so a red subtree costs only the elapsed time.
