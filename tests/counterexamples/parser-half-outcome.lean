/-
`ParserHalfForOutcome` at two actual runs: one the parser accepts and one it
refuses.

`ParserHalfForOutcome` (`LeanLLVM/Refinement/JsonPipelineRefine.lean`) is the
premise `pipeline_satisfies_of_parser` and `pipeline_units_finalisation` now
take.  It reads the verdict, the returned memory and the caller's slots out of
the run's outcome, so the only runs it can be asked about are ones an execution
produces.  This file checks that shape by instantiating it at two of them,
proved here rather than assumed:

* `acceptRun` — a function whose entry block returns `1`, run at `EntryState`
  with a memory holding the document `null`.  `parseBytes Limits.default`
  accepts `null` (`nullDocument_parses`, from `parseRef_complete` at the
  `ValidDocument` witness), so the acceptance equivalence holds at `1` and the
  accepted tape, its decode, its span discipline and its validity come from
  `decodeTape_correct` and `tape_valid`.
* `refuseRun` — the same shape returning `0`, over a byte-order mark.
  `parseBytes` refuses that document at its second branch, so the equivalence
  holds at `0` by `decide`.

The two runs differ only in the block's returned constant and the document, and
each theorem states its conclusion at the run's own outcome — `∃ o, runFuel … =
some o ∧ ParserHalfForOutcome … o` — so the outcome is not chosen by hand.

**The arena/event relation.**  `ParserHalf` requires the relation at every
readable prefix of the two buffers, and its docstring records why: the extents
are named by the units' post and by `Sigma_pipeline` rather than by this
predicate.  The relation here is the one that survives that: each readable
prefix is a prefix of the bytes the run reported at that slot.  The two slots
hold one byte each and have nothing at the following address, so the readable
prefixes are `[]` and `[b]`, and both are prefixes of `[b]`.

Run from the repository root:

    nix develop -c probes/install/mem-capped.sh --cap 6G -- \
      lake env lean tests/counterexamples/parser-half-outcome.lean
-/
import LeanLLVM.Refinement.JsonPipelineRefine
import LeanLLVM.JSON.Correct

set_option autoImplicit false

namespace LeanLLVMTest.ParserHalfOutcome

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement

/-! ### The buffers' relation

`ParserHalf` applies the event/arena relation at every readable prefix, so the
relation below is prefix-closed: every prefix of what a slot yields is a prefix
of what the run reported there. -/

/-- `xs` is a prefix of `ys`. -/
def PrefixOf (xs ys : List UInt8) : Prop := ∃ zs, ys = xs ++ zs

theorem prefixOf_nil (ys : List UInt8) : PrefixOf [] ys := ⟨ys, rfl⟩

theorem prefixOf_self (ys : List UInt8) : PrefixOf ys ys := ⟨[], by simp⟩

/-- The relation: whatever a buffer yields is a prefix of the run's own bytes at
that buffer.  `bs` and the tokens are not constrained by this relation; the
parser's answers are the other two conjuncts' business. -/
def reportRel (arenaBytes eventsBytes : List UInt8) : EventStreamRel :=
  fun _ arena evs _ => PrefixOf arena arenaBytes ∧ PrefixOf evs eventsBytes

/-! ### The ABI slots and the two memories

Twenty arguments at `pipeline.h`'s shape: the document at `base`, the caller's
slots at `dstSlot` (a one-byte arena), `evSlot` (a one-byte event buffer),
`ndstSlot`/`nevSlot` (eight-byte cursor words, both reporting extent `1`) and
`errSlot`, which holds nothing — the run reports no refusal word, which makes the
refusal-offset conjunct vacuous at both verdicts. -/

def base : Nat := 0
def dstSlot : Nat := 8
def evSlot : Nat := 16
def ndstSlot : Nat := 24
def nevSlot : Nat := 32
def errSlot : Nat := 40
def arenaByte : UInt8 := 0x07
def eventByte : UInt8 := 0x01

/-- The document `null`. -/
def readAccept : List UInt8 := [0x6E, 0x75, 0x6C, 0x6C]

/-- A byte-order mark, which `parseBytes` refuses at its own branch. -/
def readRefuse : List UInt8 := [0xEF, 0xBB, 0xBF]

/-- The argument list: the document's length, the five slots, and the two
capacities (both `64`). -/
def pargs (n : Nat) : List LeanLLVM.Value :=
  [.ptr 0, .int 64 (BitVec.ofNat 64 n), .ptr 100, .ptr 120, .ptr 140, .ptr 150,
   .int 64 256, .ptr 200, .ptr 220, .int 64 256, .ptr 240, .ptr 260,
   .ptr dstSlot, .int 64 64, .ptr ndstSlot, .ptr evSlot, .int 64 64,
   .ptr nevSlot, .ptr errSlot, .int 64 0]

/-- The cells `null` occupies at `base`, then the two buffer bytes and the two
cursor words.  Both words are the encoding of extent `1`. -/
def cellsAccept : Mem :=
  [(0, 0x6E), (1, 0x75), (2, 0x6C), (3, 0x6C),
   (8, 0x07), (16, 0x01),
   (24, 1), (25, 0), (26, 0), (27, 0), (28, 0), (29, 0), (30, 0), (31, 0),
   (32, 1), (33, 0), (34, 0), (35, 0), (36, 0), (37, 0), (38, 0), (39, 0)]

/-- The same memory over the byte-order mark. -/
def cellsRefuse : Mem :=
  [(0, 0xEF), (1, 0xBB), (2, 0xBF),
   (8, 0x07), (16, 0x01),
   (24, 1), (25, 0), (26, 0), (27, 0), (28, 0), (29, 0), (30, 0), (31, 0),
   (32, 1), (33, 0), (34, 0), (35, 0), (36, 0), (37, 0), (38, 0), (39, 0)]

/-- The two executions: one block, no instructions, a returned constant. -/
def retFn (v : Nat) : Function where
  name := "verdict"
  retTy := .int 64
  params := []
  blocks := [{ name := "entry", instrs := [],
               term := .ret (.int 64) (some (.imm (.int 64 (BitVec.ofNat 64 v)))) }]

/-! ### The parser's answers at the two documents

Nothing here is evaluated by the kernel: `parseBytes` does not reduce, so the
accepted document's tape comes from `parseRef_complete` at a validity witness and
the refused one's equation is the branch `parseBytes` itself decides. -/

theorem null_valid : ValidDocument (ByteString.literal readAccept)
    (.null : LeanLLVM.JSON.Value) :=
  ⟨⟨0, 4, by decide, ValueAt.null (by unfold HasPrefix; decide), by decide⟩,
    charPolicy_null⟩

theorem null_parses : ∃ t : Tape,
    parseBytes Limits.default (ByteString.literal readAccept) = .ok t := by
  obtain ⟨t, ht, -, -⟩ := parseRef_complete Limits.default
    (ByteString.literal readAccept) (.null : LeanLLVM.JSON.Value) null_valid
    (by decide) (by decide) (by decide)
  exact ⟨t, ht⟩

theorem bom_refused :
    parseBytes Limits.default (ByteString.literal readRefuse) =
      .error (.invalid .byteOrderMark) := by
  decide

theorem bom_no_parse : ¬ ∃ t : Tape,
    parseBytes Limits.default (ByteString.literal readRefuse) = .ok t := by
  rintro ⟨t, h⟩
  rw [bom_refused] at h
  exact nomatch h

/-! ### A buffer with only an empty and a one-byte prefix

The two cursor words report extent `1`, the buffers hold one byte each, and the
byte after each buffer's byte is absent.  So the readable prefixes of `dstSlot`
are `[]` and `[arenaByte]` and every one of them is a prefix of the reported
bytes. -/

theorem prefixes_of (m : Mem) (a : Nat) (b : UInt8)
    (h0 : readBytes m a 0 = some [])
    (h1 : readBytes m a 1 = some [b])
    (h2 : ∀ j, readBytes m a (j + 2) = none) :
    ∀ n (xs : List UInt8), readBytes m a n = some xs → PrefixOf xs [b] := by
  intro n
  cases n with
  | zero =>
      intro xs h
      rw [h0] at h
      have hxs : xs = [] := (Option.some.inj h).symm
      subst hxs
      exact prefixOf_nil _
  | succ k =>
      cases k with
      | zero =>
          intro xs h
          rw [h1] at h
          have hxs : xs = [b] := (Option.some.inj h).symm
          subst hxs
          exact prefixOf_self _
      | succ j =>
          intro xs h
          rw [h2 j] at h
          exact nomatch h

/-! ### The parser half at each document

The three conjuncts `ParserHalf` carries, at the memory and slots above: the
acceptance equivalence at the run's verdict, the accepted tape and its meaning,
and the refusal offset — the last vacuous because `errSlot` holds no word. -/

/-- The accepting instance: verdict `1`, document `null`, the arena and event
buffers reporting one byte each. -/
theorem halfAccept : ParserHalf (reportRel [arenaByte] [eventByte]) readAccept 1
    cellsAccept dstSlot evSlot errSlot := by
  intro ndst' nev' arena evs h1 h2
  have har : PrefixOf arena [arenaByte] :=
    prefixes_of cellsAccept dstSlot arenaByte rfl rfl (fun _ => rfl) ndst' arena h1
  have hev : PrefixOf evs [eventByte] :=
    prefixes_of cellsAccept evSlot eventByte rfl rfl (fun _ => rfl) nev' evs h2
  refine ⟨⟨fun _ => null_parses, fun _ => rfl⟩, ?_, ?_⟩
  · intro _
    obtain ⟨t, ht⟩ := null_parses
    obtain ⟨v, hdec, hin, hvalid⟩ :=
      decodeTape_correct Limits.default (ByteString.literal readAccept) t ht
    exact ⟨t, v, ht, hin, hdec, ⟨har, hev⟩, (tape_valid t v hdec).1, hvalid⟩
  · intro e he
    rw [show readBytes cellsAccept errSlot 8 = none from rfl] at he
    exact nomatch he

/-- The refusing instance: verdict `0`, a byte-order mark, and the same buffers.
The accepted conjunct is vacuous at `0`, so the buffers' relation is not consumed
here; the refusal word is absent from `errSlot` as in the accepting case. -/
theorem halfRefuse : ParserHalf (reportRel [arenaByte] [eventByte]) readRefuse 0
    cellsRefuse dstSlot evSlot errSlot := by
  intro ndst' nev' arena evs h1 h2
  refine ⟨⟨fun h => absurd h (by decide), fun hex => absurd hex bom_no_parse⟩, ?_, ?_⟩
  · intro h
    exact absurd h (by decide)
  · intro e he
    rw [show readBytes cellsRefuse errSlot 8 = none from rfl] at he
    exact nomatch he

/-! ### The instantiation, at the runs' own outcomes -/

/-- The accepting execution returns `1` over `null`, and the parser half holds at
that outcome. -/
theorem accept_half :
    ∃ o, runFuel noCalls 1 (retFn 1)
        (EntryState (retFn 1) (pargs 4) cellsAccept 1) = some o ∧
      ParserHalfForOutcome (reportRel [arenaByte] [eventByte]) base (pargs 4)
        cellsAccept o := by
  refine ⟨.ret (some (.int 64 1)) cellsAccept, rfl, ?_⟩
  unfold ParserHalfForOutcome pargs
  exact ⟨readAccept, rfl, rfl, halfAccept⟩

/-- The refusing execution returns `0` over a byte-order mark, and the parser
half holds at that outcome. -/
theorem refuse_half :
    ∃ o, runFuel noCalls 1 (retFn 0)
        (EntryState (retFn 0) (pargs 3) cellsRefuse 1) = some o ∧
      ParserHalfForOutcome (reportRel [arenaByte] [eventByte]) base (pargs 3)
        cellsRefuse o := by
  refine ⟨.ret (some (.int 64 0)) cellsRefuse, rfl, ?_⟩
  unfold ParserHalfForOutcome pargs
  exact ⟨readRefuse, rfl, rfl, halfRefuse⟩

/-! ### Axiom footprints

Each theorem is a closed proof over the parser's own correctness statements; no
new principle enters.  The pins are measured rather than assumed. -/

/-- info: 'LeanLLVMTest.ParserHalfOutcome.PrefixOf' does not depend on any axioms -/
#guard_msgs in
#print axioms PrefixOf

/-- info: 'LeanLLVMTest.ParserHalfOutcome.null_parses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms null_parses

/-- info: 'LeanLLVMTest.ParserHalfOutcome.bom_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bom_refused

/-- info: 'LeanLLVMTest.ParserHalfOutcome.halfAccept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms halfAccept

/-- info: 'LeanLLVMTest.ParserHalfOutcome.halfRefuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms halfRefuse

/-- info: 'LeanLLVMTest.ParserHalfOutcome.accept_half' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms accept_half

/-- info: 'LeanLLVMTest.ParserHalfOutcome.refuse_half' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refuse_half

end LeanLLVMTest.ParserHalfOutcome
