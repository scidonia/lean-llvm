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

The frame clause had the same defect in a conjunct rather than in the parser half.
An earlier `pipeline_satisfies_of_parser` took `SigmaFrame args outcome mem` over
every argument list, memory and outcome, so an *empty* returned memory was in its
scope.  `SigmaFrame` asks `pipelineOutputExtents`, whose two cursor reads must
succeed at the outcome's memory; the empty memory answers neither, so the
statement is false as a universal.  `pipeline_frame_hsem_false` below is that
regression.  The frame is now derived from the units' post at the run's own
outcome rather than assumed, and the false universal is why it cannot be a
premise at any narrower shape either: its extent component is a reading of the
returned memory, not a property of the argument list.

The event-length equality the walk's invariant used to carry is the third: it
required the event cursor to be `nev0 + 13 * records`, but the stream's encoding
is variable-width (one, nine or thirteen bytes), so a literal's emission and a
number's emission each supply a cursor with no natural-number record count.
`stage2_evlen_thirteen_eq_false` and `stage2_evlen_thirteen_eq_false_number` are
the two instances.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonStage2WalkScope

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

/-- The witness argument list: the ABI's twenty slots.  Positions fifteen and
eighteen are the arena and event cursor slots (`ndst`, `nev`), and the empty
returned memory below has neither. -/
private def frameArgs : List LeanLLVM.Value :=
  [.ptr 1000, .int 64 4, .ptr 0, .ptr 8, .ptr 16, .ptr 24, .int 64 0, .ptr 32,
   .ptr 40, .int 64 0, .ptr 48, .ptr 56, .ptr 64, .int 64 0, .ptr 0, .ptr 72,
   .int 64 0, .ptr 8, .ptr 96, .int 64 0]

/-- **`SigmaFrame` is false as a universal.**

The hypothesis is the premise `pipeline_satisfies_of_parser` used to take —
`SigmaFrame` at every argument list, memory and outcome.  The proof instantiates it
at the shaped argument list above, an arbitrary starting memory, and the outcome
that returns a word in an **empty** memory.  `SigmaFrame` then asks
`pipelineOutputExtents`, which requires the eight bytes at the arena and event
cursor slots of *that* memory; the empty memory has none, so the word's own
eight-byte reads fail and the statement is uninhabited.  The frame is derived at
the run's own outcome for this reason: its extent component reads the returned
memory, so no argument list and no starting memory decides it. -/
theorem pipeline_frame_hsem_false :
    ¬ (∀ (args : List LeanLLVM.Value) (mem : Mem) (o : Outcome), SigmaFrame args o mem) := by
  intro h
  have hf := h frameArgs ([] : Mem) (.ret (some (.int 64 0)) ([] : Mem))
  have hnone : readBytes ([] : Mem) 0 8 = none := rfl
  -- The frame's witness block is thirteen numbers: the four cursors and the
  -- stage-2 callee's nine private objects.  Its extents' conjunct then reads
  -- the returned memory at `frameArgs`' cursor slots (`ndst = 0`, `nev = 8`),
  -- and the empty memory answers neither eight-byte read.
  simp only [SigmaFrame, frameArgs, pipelineOutputExtents, hnone] at hf
  simp at hf

/-- **The retired event-length equality is false at a literal's emission.**  A
container marker or a literal — here a root `true` — writes one byte through
`out_tag`, so the carry's trace is `[tag 1]` and the cursor is `nev0 + 1`.  The
retired invariant said the cursor is `nev0 + 13 * records`, which no
natural-number `records` satisfies at that trace. -/
theorem stage2_evlen_thirteen_eq_false (nev0 records : Nat) :
    ¬ (nev0 + ([EventRecord.tag 1].map EventRecord.encodedSize).sum =
        nev0 + stage2RecordBytes * records) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EventRecord.encodedSize_tag, stage2RecordBytes]
  omega

/-- **The same at a number's emission.**  A number's record is nine bytes (the
tag and the binary64 payload), so `nev0 + 9 = nev0 + 13 * records` has no
natural-number solution either. -/
theorem stage2_evlen_thirteen_eq_false_number (nev0 records bits : Nat) :
    ¬ (nev0 + ([EventRecord.number bits].map EventRecord.encodedSize).sum =
        nev0 + stage2RecordBytes * records) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EventRecord.encodedSize_number, stage2RecordBytes]
  omega

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

/-- info: 'LeanLLVMTest.Counterexamples.pipeline_frame_hsem_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_frame_hsem_false

/-- info: 'LeanLLVMTest.Counterexamples.stage2_evlen_thirteen_eq_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2_evlen_thirteen_eq_false

/-- info: 'LeanLLVMTest.Counterexamples.stage2_evlen_thirteen_eq_false_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2_evlen_thirteen_eq_false_number

end LeanLLVMTest.Counterexamples
