/-
The contracted stage-1 block unit's boundary record.

`Γ_s1_blocks` is the record the pipeline's single call is resolved at: the
caller stages the padded document, the entry array, the escape stream and its
count slot, and the carry's sixteen bytes; the run returns the ASCII probe, the
entry words, and — on the gate's arm — the escape list.  The post's substance is
`s1BlocksPost`; this module fixes the pre, the budget and the two relations a
call site needs (`ValueIrrelevant` is deliberately absent: the return word is
observable, so the record's post reads it).

The budget is a term of the arguments: the loop's four control steps per block
plus the entry, preheader, cleanup, the peeled block and the done block.  It is
the plan's `4 * blocks + 8`; the peeled tail's own steps are inside the constant
because the tail is one block whatever the document's length.

`s1_blocks_refines` states the body's run at this staging and
`s1_blocks_satisfies` will be its record instance.  Neither is stated in this
module: the record is here so a call site has one place to resolve against.
-/
import LeanLLVM.Refinement.JsonS1BlocksSteps
import LeanLLVM.Refinement.Relation

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

/-- The document's length, as the ABI's second argument.  `none` when the
argument list is not the unit's. -/
def s1BlocksLength (args : List Value) : Option Nat :=
  match args with
  | [.ptr _, .int 64 n, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 _] => some n.toNat
  | _ => none

/-- The run's fuel: four control steps per block plus the constant blocks around
the loop. -/
def s1BlocksBudget (args : List Value) (_mem : Mem) : Nat :=
  match s1BlocksLength args with
  | some n => 4 * blocksOf n + 8
  | none => 0

/-- The caller's staging.  The document is the padded window the classifier
reads; `ent` and the escape stream are the caller's; the count slot holds the
stream's initial cursor; the carry is the all-false pair; and the four objects
are separate. -/
def s1BlocksPre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (b ent xp nxp xcarry : Nat) (arm : BitVec 64) (bs : List UInt8) (xn : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
            .ptr nxp, .ptr xcarry, .int 64 arm] ∧
    readBytes mem b (64 * blocksOf bs.length) = some (padded bs) ∧
    HasBytes mem ent (8 * blocksOf bs.length) ∧
    readBytes mem nxp 8 = some (wordBytes 8 xn) ∧
    xn < 2 ^ 63 ∧
    HasBytes mem xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)) ∧
    readBytes mem xcarry 16 = some (flagBytes false ++ flagBytes false) ∧
    blocksOf bs.length * 64 + 63 < 2 ^ 32 ∧
    -- the four objects the run may write are pairwise separate, and the window
    -- it reads is separate from all of them
    (b + 64 * blocksOf bs.length ≤ ent ∨ ent + 8 * blocksOf bs.length ≤ b) ∧
    (ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ ent) ∧
    (ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent) ∧
    (ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ ent) ∧
    (xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
      nxp + 8 ≤ xp) ∧
    (xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
      xcarry + 16 ≤ xp) ∧
    (nxp + 8 ≤ xcarry ∨ xcarry + 16 ≤ nxp)

/-- The contracted block unit's boundary record.  Its post refuses `ub` and reads
the return word; the budget is the loop's cost as a term of the document's
length. -/
def Γ_s1_blocks : MemContract where
  budget := s1BlocksBudget
  pre := s1BlocksPre
  post := fun args mem next o => s1BlocksPost args mem next o

end LeanLLVM.Refinement.JsonS1BlocksSteps
