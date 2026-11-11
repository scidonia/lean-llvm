/-
Counterexamples to the semantic premises the final parser composition retired.

`pipeline_satisfies_of_parser` and `pipeline_units_finalisation`
(`LeanLLVM.Refinement.JsonPipelineRefine`) used to take the parser
correspondence as a hypothesis quantified over the document, the verdict, the
returned memory and the caller's slots:

    ∀ mem bs verdict m dst ev err ndst' nev',
      readBytes mem base bs.length = some bs →
      ParserHalf eventRel bs verdict m dst ev err ndst' nev'

`ParserHalf` carries `verdict = 1 ↔ ∃ t, parseBytes Limits.default … = .ok t`
as its first conjunct.  The quantifier ran over `verdict`, so one input supplied
the acceptance equivalence at `1` and at `0`; the first says the parser accepts,
the second says it does not.  Both declarations now take
`ParserHalfForOutcome`, whose verdict is a field of the run's outcome.

The input read is the `readBytes` hypothesis of that retired premise.  The empty
document supplies it in every memory and at every base, because
`readBytes m a 0 = some []` is the definition's first branch, so the
contradiction needs no concrete `Mem`, no concrete `base`, and no evaluation of
the parser's answer.  The two lemmas below state this at an arbitrary
`eventRel` (and, for the finalisation's, at an arbitrary staging memory and
`base`), which is every instance the retired theorems could be used at.
-/
import LeanLLVM

namespace LeanLLVMTest.Counterexamples

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement

/-! ### The two verdict values the contradiction uses

`ParserHalf`'s first conjunct is read at `verdict = 1` and at `verdict = 0`.
These two facts are what make those reads incompatible, and each is decided
rather than assumed — the second by `decide` on the `BitVec 64` equality. -/

/-- The accepting instance's antecedent. -/
theorem verdict_one_eq : (1 : BitVec 64) = 1 := rfl

/-- The refusing instance's verdict is not the accepting one. -/
theorem verdict_zero_ne_one : ¬ ((0 : BitVec 64) = 1) := by decide

/-- **The universally quantified parser half is false.**

The hypothesis is the one `pipeline_satisfies_of_parser` took, at an arbitrary
`eventRel` and `base`.  The proof instantiates it on the empty document and the
empty memory at `verdict = 1` and at `verdict = 0`, reads the acceptance
equivalence out of `ParserHalf` both times, and derives the contradiction. -/
theorem pipeline_parser_hsem_false (eventRel : EventStreamRel) (base : Nat) :
    ¬ (∀ (mem : Mem) (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
        (dst ev err ndst' nev' : Nat),
        readBytes mem base bs.length = some bs →
        ParserHalf eventRel bs verdict m dst ev err ndst' nev') := by
  intro hsem
  -- The empty document reads in the empty memory at any base.
  have hread : readBytes ([] : Mem) base ([] : List UInt8).length = some [] := rfl
  have h1 := hsem ([] : Mem) [] 1 ([] : Mem) 0 0 0 0 0 hread
  have h0 := hsem ([] : Mem) [] 0 ([] : Mem) 0 0 0 0 0 hread
  -- The acceptance equivalence at `1`: the parser accepts the empty document.
  have hacc : ∃ t : Tape,
      parseBytes Limits.default (ByteString.literal ([] : List UInt8)) = .ok t :=
    h1.1.mp rfl
  -- The acceptance equivalence at `0`: the parser does not accept it.
  have hlt : (0 : BitVec 64) = 1 := h0.1.mpr hacc
  exact absurd hlt verdict_zero_ne_one

/-- **The finalisation's retired premise is false as well.**

`pipeline_units_finalisation` took the same universally quantified parser half,
at the staging's own memory and base.  Its `readBytes` premise is the one that
pins the document, and the empty document satisfies it in every memory and at
every base, so the contradiction is the previous lemma's at an arbitrary
staging: the equivalence is demanded at `verdict = 1` and at `verdict = 0`. -/
theorem pipeline_units_finalisation_hsem_false (eventRel : EventStreamRel)
    (mem : Mem) (base : Nat) :
    ¬ (∀ (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
        (dst ev err ndst' nev' : Nat),
        readBytes mem base bs.length = some bs →
        ParserHalf eventRel bs verdict m dst ev err ndst' nev') := by
  intro hsem
  have hread : readBytes mem base ([] : List UInt8).length = some [] := rfl
  have h1 := hsem [] 1 ([] : Mem) 0 0 0 0 0 hread
  have h0 := hsem [] 0 ([] : Mem) 0 0 0 0 0 hread
  have hacc : ∃ t : Tape,
      parseBytes Limits.default (ByteString.literal ([] : List UInt8)) = .ok t :=
    h1.1.mp rfl
  have hlt : (0 : BitVec 64) = 1 := h0.1.mpr hacc
  exact absurd hlt verdict_zero_ne_one

/-! ### Axiom footprint

Each lemma is a closed proof: it consumes no parser result and adds no principle,
so both sit at the development's ceiling.  The pins are measured rather than
assumed. -/

/-- info: 'LeanLLVMTest.Counterexamples.pipeline_parser_hsem_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_parser_hsem_false

/-- info: 'LeanLLVMTest.Counterexamples.pipeline_units_finalisation_hsem_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_units_finalisation_hsem_false

end LeanLLVMTest.Counterexamples
