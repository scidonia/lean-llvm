/-
The contracted stage-1 block unit's boundary record.

`Γ_s1_blocks` is the record the pipeline's single call is resolved at: the
caller stages the three zero bytes before the padded document, the entry array,
the escape stream and its count slot, and the carry's sixteen bytes; the run
returns a two-bit word (the ASCII probe in bit 0 and the UTF-8 stage's error word
in bit 1), the entry words, and — on the gate's arm — the escape list.  The
post's substance is `s1BlocksPost`; this module fixes the pre, the budget and
the two relations a call site needs (`ValueIrrelevant` is deliberately absent:
the return word is observable, so the record's post reads it).

The budget is a term of the arguments: eight control steps per block plus the
entry, preheader, cleanup, the peeled block and the done block.  The fused loop's
worst path adds the DFA arm and the escape arm to the latch, so the emitted
CFG's per-block bound is five; the budget keeps slack and is stated at eight.
The peeled tail's own steps are inside the constant because the tail is one
block whatever the document's length.

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

/-- The run's fuel: eight control steps per block plus the constant blocks
around the loops.  A block's worst path is `for.body54` → the DFA arm (or
`if.end93`) → the escape-list arm (or `if.end98`) → the latch: five control
steps.  The leading ASCII phase is shorter per block, and the hand-off's DFA
step and the tail's DFA and escape arms are the constant part.  Eight is that
bound with slack, not a tight count; the emitted CFG is in `JsonS1BlocksIR`. -/
def s1BlocksBudget (args : List Value) (_mem : Mem) : Nat :=
  match s1BlocksLength args with
  | some n => 8 * blocksOf n + 32
  | none => 0

/-- The caller's staging.  The document is the padded window the classifier
reads; the three bytes before it are the UTF-8 DFA's zero load-form carry;
`ent` and the escape stream are the caller's; the count slot holds the stream's
initial cursor; the carry is the all-false pair; the four objects are pairwise
separate; and the window, with the three bytes before it, is separate from all
four.  `3 ≤ b` is what makes the three prefix bytes addressable, and
`bs.length < 2 ^ 63` is `utf8.h`'s bound on the block count. -/
def s1BlocksPre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (b ent xp nxp xcarry : Nat) (arm : BitVec 64) (bs : List UInt8) (xn : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
            .ptr nxp, .ptr xcarry, .int 64 arm] ∧
    3 ≤ b ∧
    readBytes mem (b - 3) 3 = some [0, 0, 0] ∧
    bs.length < 2 ^ 63 ∧
    readBytes mem b (64 * blocksOf bs.length) = some (padded bs) ∧
    HasBytes mem ent (8 * blocksOf bs.length) ∧
    readBytes mem nxp 8 = some (wordBytes 8 xn) ∧
    xn < 2 ^ 63 ∧
    HasBytes mem xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)) ∧
    readBytes mem xcarry 16 = some (flagBytes false ++ flagBytes false) ∧
    blocksOf bs.length * 64 + 63 < 2 ^ 32 ∧
    -- the four objects the run may write are pairwise separate; the window it
    -- reads, together with the three staged bytes before it, is separate from
    -- all four, so the loop's entry stores and the escape call's stream, count
    -- and carry writes cannot reach a document block or the staged zeroes.
    -- `ent` is separate from the prefix too, because the first block's entry
    -- store precedes its DFA arm
    (b + 64 * blocksOf bs.length ≤ ent ∨
      ent + 8 * blocksOf bs.length ≤ b - 3) ∧
    (b + 64 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ b - 3) ∧
    (b + 64 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ b - 3) ∧
    (b + 64 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ b - 3) ∧
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
