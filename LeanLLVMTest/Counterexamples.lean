/-
A counterexample to the semantic premise of the final parser composition.

`pipeline_satisfies_of_parser` (`LeanLLVM.Refinement.JsonPipelineRefine`) takes
the parser correspondence as a hypothesis quantified over the document, the
verdict, the returned memory and the caller's slots:

    ∀ mem bs verdict m dst ev err,
      readBytes mem base bs.length = some bs →
      ParserHalf eventRel bs verdict m dst ev err

`ParserHalf` carries `verdict = 1 ↔ ∃ t, parseBytes Limits.default … = .ok t`
as its first conjunct.  The quantifier runs over `verdict`, so one input
supplies the acceptance equivalence at `1` and at `0`; the first says the parser
accepts, the second says it does not.

The input read is the `readBytes` hypothesis of that theorem's own hypothesis.
The empty document supplies it in every memory and at every base, because
`readBytes m a 0 = some []` is the definition's first branch, so the
contradiction needs no concrete `Mem`, no concrete `base`, and no evaluation of
the parser's answer.  The lemma below states this at an arbitrary `eventRel` and
`base`, which is every instance the theorem can be used at.
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

The hypothesis is the one `pipeline_satisfies_of_parser` takes, at an arbitrary
`eventRel` and `base`.  The proof instantiates it on the empty document and the
empty memory at `verdict = 1` and at `verdict = 0`, reads the acceptance
equivalence out of `ParserHalf` both times, and derives the contradiction. -/
theorem pipeline_parser_hsem_false (eventRel : EventStreamRel) (base : Nat) :
    ¬ (∀ (mem : Mem) (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
        (dst ev err : Nat),
        readBytes mem base bs.length = some bs →
        ParserHalf eventRel bs verdict m dst ev err) := by
  intro hsem
  -- The empty document reads in the empty memory at any base.
  have hread : readBytes ([] : Mem) base ([] : List UInt8).length = some [] := rfl
  have hzero : readBytes ([] : Mem) 0 0 = some [] := rfl
  have h1 := hsem ([] : Mem) [] 1 ([] : Mem) 0 0 0 hread
  have h0 := hsem ([] : Mem) [] 0 ([] : Mem) 0 0 0 hread
  -- The acceptance equivalence at `1`: the parser accepts the empty document.
  have hacc : ∃ t : Tape,
      parseBytes Limits.default (ByteString.literal ([] : List UInt8)) = .ok t :=
    (h1 0 0 [] [] hzero hzero).1.mp rfl
  -- The acceptance equivalence at `0`: the parser does not accept it.
  have hlt : (0 : BitVec 64) = 1 := (h0 0 0 [] [] hzero hzero).1.mpr hacc
  exact absurd hlt verdict_zero_ne_one

/-! ### Axiom footprint

The lemma is a closed proof: it consumes no parser result and adds no principle,
so it sits at the development's ceiling.  The pin is measured rather than
assumed. -/

/-- info: 'LeanLLVMTest.Counterexamples.pipeline_parser_hsem_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_parser_hsem_false

end LeanLLVMTest.Counterexamples
