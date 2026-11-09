/-
The assembled pipeline's specification: the verdict, the event stream and the
first error offset against the reference parser.

`JsonPipelineContract` states the record the assembled body satisfies,
`Γ_pipeline_units` — a boundary projection about the buffers the run leaves.
This module states the *specification* record `Γ_pipeline`, whose post
`Sigma_pipeline` is the reference parser's predicate at
`LeanLLVM.JSON.Limits.default` (`Parse.lean:34`: one mebibyte of input, 128
levels, one mebi tokens) rather than a description of the body's buffers.  The
plan writes this predicate `Σ_pipeline`; the toolchain does not accept `Σ` in an
identifier, so the declaration below is `Sigma_pipeline` — the same object under
the toolchain's spelling.

The body's record is an object with a definition, a budget and a post about the
buffers the run leaves; a record whose post were `Sigma_pipeline` would make the
pipeline's proof depend on a predicate that module does not constrain.  D2
composes the two with `Satisfies.mono` (`Refinement.lean:258`), whose post
hypothesis `Γ_pipeline_units.post → Sigma_pipeline` is the finalisation lemma;
the pre and the budget below read the body's staging and fuel by name, so that
step's other two hypotheses are the identity and only the finalisation is work.

# Clause by clause, and where each clause comes from

Nothing here is a new promise.  Each conjunct is the caller-side staging clause,
the boundary fact, or the parser relation that an existing record or header
already states, read at the pipeline's twenty-argument ABI
(`pipeline.h:33-37`, `pipelineBody.params`):

* **the argument shape** — `pipeline.h:33-37` and the staging's own pattern
  (`JsonPipelineContract.lean:229`);
* **the input relation** `readBytes mem base n = some bs` with
  `n = bs.length` — the staging's document clause
  (`JsonPipelineContract.lean:238-240`), which stages the padded window and the
  exact-length read inside it; `Sigma_pipeline` restates the exact-length form
  because the parser's predicate is stated over `bs`, not over the padding
  (`C102`);
* **the input bound** `bs.length ≤ Limits.default.maxInput` — the staging's
  clause, from `Parse.lean:34` (`maxInput = 1048576`); the parser refuses a
  longer document with `.inputTooLong` before it looks at the bytes
  (`Parse.lean:390-392`);
* **the non-empty document** — the staging's `0 < bs.length`
  (`JsonPipelineContract.lean`, §15.82): `Γ_utf8.pre` requires it and the entry
  test sends a zero-length document past the loop to `for.cond.cleanup`, where
  the UTF-8 stage is still called.  **The empty document is outside the
  specification's domain**: neither acceptance nor refusal at length zero is
  claimed here, and a reader must not take the parser's refusal-at-zero as a
  promise of this record;
* **the verdict word** — `pipeline.h:55-57`: the return is `1` for acceptance
  and `0` for refusal.  `Sigma_pipeline` states the two-valued disjunction and
  the equality with the parser below;
* **acceptance is `.ok` exactly when `parseBytes` is** — `Parse.lean:390-405`'s
  `ParseResult`; `parseBytes Limits.default bs = .ok t` is the parser's
  acceptance, and `.error e` its refusal;
* **the accepted value** — `decodeTape t = some v` (`Tape.lean:316-324`) is the
  parser's value, and `spansWellFormed t = true ∧ ValidDocument bs v` is
  `tape_valid`'s conclusion (`TapeCorrect.lean:1041-1043`) read at that value:
  the tape's spans check out against its own input and its input names a text of
  the accepted language (`Spec.lean:486`);
* **the event stream** — `stage2.h:68-75` fixes the measured encoding (a tag
  byte for the structural bytes and the three literals, a tag plus eight IEEE
  bytes for a number, and a tag, a four-byte length and an eight-byte
  span-or-arena field for a key or a string; `stage2.c:127-128`, `:837-842`).
  `EventStreamRel` below is C95's relation between that record stream and
  `Tape`'s tokens, and is a *parameter* of this record for the reason
  `JsonPipelineIR.lean:52-56` gives for `stage2Sel`: `JsonStage2Spec.lean` is
  not in this tree at this revision.  With it, the plan's "the event stream's
  decode equals `decodeTape`'s value" is the consequence of the relation and
  `decodeTape t = some v`, not a second decoder stated here;
* **the refusal offset** — `pipeline.h:37` (`*err` is the first error offset on
  refusal) and `pipeline.c:68-73`.  `RefusalOffset` below splits by the stage
  that owns the refusal, because the measured caller does: a non-zero UTF-8
  stage word writes `*err = n` (`pipeline.c:71-73`; the stage reports that the
  document is invalid, not where, `stage2.h:60-62`), while the entry walk's own
  refusals carry the parser's position (`Parse.lean:38-56`).  The split is
  executed evidence, not prose: `parseBytes Limits.default` on
  `[0x22, 0x80, 0x22]` returns `.error (.invalid (.badUTF8 1))` (evaluated), and
  the caller writes `*err = n = 3` (`pipeline.c:71-73`), so the offsets differ
  for a constructor that carries a position;
* **the unchanged conjunct** — every unit's post carries "unchanged outside the
  extent the run wrote" (`JsonEscapeSteps.lean:85-88`, and the same clause in
  `Γ_masks`, `Γ_entry_pos8`, `Γ_entry_b8`, `Γ_utf8`).  The extents are the ones
  the units' own posts name, not the staged capacities: the entry stream's
  written prefix is `4 * (nk' + 8)` (the emitter's frame, with its eight-entry
  reserve, `JsonUnitContracts.lean:857-861`); the escape list's is
  `4 * (nxp' + 8)` (the batch's eight-entry reserve, `JsonEscapeSteps.lean:130-133`
  and the record's frame at `:223`); the arena's is `ndst' + 64` (the expander's
  decoding slack, `stage2.h:78-81`); the event stream's is `nev'` (stage 2
  appends, `stage2.h:13-21`); the three scratch slots `sc`/`mk`/`entw`, the
  escape carry `xcarry` (`pipeline.h:19-24`) and the five cursor slots are at
  their header sizes.  The document at `base` is deliberately not in the list,
  so **the pipeline is stated not to modify its input** — the clause every other
  record carries, and the one a caller would notice first if it moved.  The
  escape list's batch overshoot and the UTF-8 stage's unchanged memory are both
  inside these extents or inside a region the body never writes (`C119`;
  `utf8Post`'s `m = mem`, `JsonUnitContracts.lean:819`).

# The exclusions, named as clauses of the statement

* **an input over the input bound** — `bs.length ≤ Limits.default.maxInput`, a
  conjunct of the staging, so a longer document is outside the domain;
* **depth and token exhaustion** — `pipelineSpecPre` requires that
  `parseBytes Limits.default bs` does not return `.depthExceeded` or
  `.outOfCapacity`.  This matters: the pipeline's ABI has no depth or token
  limit (`pipeline.h:33-37`), while the parser refuses a document nested deeper
  than `maxDepth` or carrying more tokens than `maxTokens` (`Limits`,
  `Parse.lean:30-35`), so the pipeline may accept a document the parser refuses.
  The exclusion is stated rather than discovered later.  (Token exhaustion is in
  fact unreachable under the input bound — every token occupies at least one
  byte, so `tokens ≤ bs.length ≤ maxInput = maxTokens` — but the clause is
  retained because it is the parser's policy, not a consequence of the
  pipeline.);
* **capacity and allocation failure** — outside the claim: every buffer is the
  caller's (`pipeline.h:13-25`, `stage2.h:10-30`), the body has no `alloca` and
  no `llvm.memset` (`JsonPipelineIR.lean`'s `allocaTypes = []`), and a caller
  that under-reserves is outside every unit's `pre` (§11.2).  The staging bounds
  the entry stream, the escape list, the arena and the event stream.  The event
  clause is the header's written-buffer promise (`stage2.h:13-21`) at the
  encoding's worst case — at most one record per input byte and at most thirteen
  bytes per record, `nev0 + 13 * bs.length ≤ evcap` — and it **lives in
  `pipelineStaging`** (`JsonPipelineContract.lean`), which this record's pre
  conjoins first, so this pre is no wider than the measured code's domain.  A
  caller that under-reserves is thereby outside this record's domain rather than
  a case whose behaviour is claimed.

# What a proof of this record would need

`Sigma_pipeline` is a statement, not a theorem; the obligations D2 must discharge
are named here so the record is not read as proved:

1. **The finalisation lemma, `Γ_pipeline_units.post → Sigma_pipeline`.**  The
   boundary projection carries cursors, prefixes, the refusal word and the frame,
   but not the parser's verdict or value.  The lemma must turn the exit
   invariant plus the tail's per-unit facts into the clauses above.  In
   particular the units' post does not name `parseBytes`, so the verdict and
   offset clauses need the stage-2 post (`C95`/`C96`) and the UTF-8 post
   (`JsonUnitContracts.lean:809-819`) at the outcome the run returns; the
   `stage2_verdict_bounded` companion (§15.81) is the fact that supplies the
   two-valued verdict from the stage-2 slot.
2. **C95's `JsonStage2Spec`**, the instantiation of `EventStreamRel`.  It must
   bind each 13-byte record's tag and payload to the `Token` it names
   (`stage2.h:68-75`, `Tape.lean:40-48`).  One arm of that binding has no model
   in this tree: the number record carries the IEEE double (`stage2.c:598`),
   while `decodeTape` returns `Value.number` with the **source lexeme**
   (`Tape.lean:130-133`), so binding the two needs the lexeme→double conversion
   (`num_fast`/`strtod`, not modelled in Lean) or a value correspondence weaker
   than `Value` equality.  That clause is the reason the relation is a parameter
   here and not a definition: it is C95's deliverable, and stating it a second
   time would be two specifications of one stream.
3. **`Γ_stage2` and `stage2_satisfies`** (`C96`), absent at this revision: the
   pipeline's stage-2 call site is a slot (`JsonPipelineIR.lean:1170-1250`), and
   the finalisation lemma consumes its post.  Until it exists the record is
   stated and not proved.
4. **`tape_valid`/`decodeTape_correct`** (`TapeCorrect.lean:1041-1043`,
   `Correct.lean:4123-4145`): `decodeTape t = some v` and the validity conjuncts
   are not properties of an arbitrary tape; they come from the parser's own
   correctness theorem applied to `parseBytes ... = .ok t`.
5. **The event capacity clause lives in the staging, not here.**  The staging
   (`JsonPipelineContract.lean:229`) bounds the entry stream, the escape list,
   the arena and the event stream, the last with the header's written-buffer
   promise at the encoding's worst case, `nev0 + 13 * bs.length ≤ evcap`
   (`stage2.h:13-21`).  It was once stated here alone, and this record's note
   asked the staging's owner to carry it: a too-small event buffer was admitted
   by the staging while the measured stage 2 traps, so the body's record did not
   state the bound that makes its own domain the measured code's.  **The note is
   discharged and the clause is not repeated in `pipelineSpecPre`**, because one
   fact stated in two records is two spellings that drift — the staging is this
   pre's first conjunct, so D2's `Satisfies.mono` step needs only
   `pipelineSpecPre → pipelineStaging`, which remains a projection.
6. **The mono step.**  `Satisfies.mono` needs
   `pipelineSpecPre → pipelineStaging` (a projection of the conjunction),
   `pipelineBudget ≤ pipelineBudget` (`Nat.le_refl`), and the post implication
   above; the two trivial hypotheses are the reason the specification reuses the
   body's record's pre and budget by name instead of restating them.

The axioms of this module are pinned below; the definitions here add no
assumption.  `Sigma_pipeline` contains no `sorry`, no `admit`, and no
`native_decide`, and it quantifies only over the parser's own vocabulary.
-/
import LeanLLVM.Vellum.JsonPipelineContract
import LeanLLVM.JSON.TapeCorrect

set_option autoImplicit false

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonUtf8IR

/-! ### The event stream's relation, named rather than restated

`stage2.h:68-75` fixes the record encoding; C95's `JsonStage2Spec` states what a
record stream means against `Tape`'s tokens.  That module is not in this tree at
this revision, so the relation enters this record as a parameter — the same
deferral `stage2Sel` has (`JsonPipelineIR.lean:52-56`).  The terminal theorem
instantiates it with C95's relation, at which point the parameter is not free.
-/

/-- C95's relation: the document `bs`, the arena bytes the run decoded into, the
event bytes and the parser's tokens.  A record stream satisfying it names the
same tokens — tag and payload each bound to the token it names — so decoding it
is decoding `Tape`'s tokens, and its value is `decodeTape`'s. -/
abbrev EventStreamRel :=
  List UInt8 → List UInt8 → List UInt8 → List Token → Prop

/-! ### The ABI projections the statement's non-post clauses read

These name one field each out of the twenty-argument list at
`pipeline.h:33-37`.  They exist so the pre can name the document and the event
capacity without projecting through an existential; the post's
pattern reads the same fields and is checked against the same shape by the
`#guard`s below. -/

/-- The ABI's document length, its second argument (`pipeline.h:33`). -/
def pipelineDocLength : List Value → Option Nat
  | [.ptr _, .int 64 n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] =>
      some n.toNat
  | _ => none

/-- The ABI's event-stream capacity, its seventeenth argument
(`pipeline.h:37`). -/
def pipelineEvCapacity : List Value → Option Nat
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .int 64 evcap, _, _, _] =>
      some evcap.toNat
  | _ => none

/-- The ABI's event-count slot, its eighteenth argument. -/
def pipelineNevSlot : List Value → Option Nat
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .ptr nev, _, _] =>
      some nev
  | _ => none

/-! ### The parser's refusal positions -/

/-- The position a refusal constructor carries.  Every `Reject` constructor but
`byteOrderMark` carries the offset (`Parse.lean:38-56`); the position-free one is
matched by constructor alone, which is C22's distinction carried forward
unchanged. -/
def rejectPos : Reject → Option Nat
  | .byteOrderMark => none
  | .unexpectedEnd p => some p
  | .unexpectedByte p _ => some p
  | .badLiteral p _ => some p
  | .badNumber p => some p
  | .unterminatedString p => some p
  | .badEscape p => some p
  | .badUTF8 p => some p
  | .unpairedSurrogate p => some p
  | .noncharacter p => some p
  | .controlCharacter p => some p
  | .expectedColon p => some p
  | .expectedComma p => some p
  | .expectedCloseBracket p => some p
  | .expectedCloseBrace p => some p
  | .trailingData p => some p

/-- The first error offset, split by the stage that owns the refusal.

The measured caller validates the document's UTF-8 before it walks the entry
stream, and a non-zero stage word writes `*err = n` (`pipeline.c:68-73`; the
stage reports that the document is invalid and not where, `stage2.h:60-62`).
`utf8WinPrefix` is the stage's own validity relation (`utf8Post`,
`JsonUnitContracts.lean:809-819`).  So:

* a UTF-8-invalid document refuses at the document end, `e = bs.length`;
* a UTF-8-valid document's refusal belongs to the entry walk, and its offset is
  the parser's position, matched by constructor alone for `byteOrderMark`.

The split is executed on the parser side and read on the caller side:
`parseBytes Limits.default [0x22, 0x80, 0x22]` evaluates to
`.error (.invalid (.badUTF8 1))` and the caller writes `*err = n = 3`
(`pipeline.c:71-73`).  C102's
"the first error offset is the parser's" therefore holds for the walk's
refusals; the UTF-8 stage's document-end rule is its own, and this record states
it rather than claiming the parser's position for it. -/
def RefusalOffset (bs : List UInt8) (e : Nat) : Prop :=
  let nb := pipelineBlocks bs.length
  (utf8WinPrefix (utf8Window bs bs.length nb) →
     ∀ r : Reject, parseBytes Limits.default (ByteString.literal bs) =
                       .error (.invalid r) →
       match rejectPos r with
       | some p => e = p
       | none => True) ∧
  (¬ utf8WinPrefix (utf8Window bs bs.length nb) → e = bs.length)

/-! ### The specification precondition -/

/-- The caller's promise for the specification record: the staging the body's
record already asks for, plus the parser's policy exclusions, named in the
module docstring.  The staging is read by name from `Γ_pipeline_units`
(`JsonPipelineContract.lean:229`) — the specification claims nothing about a
caller that record would not admit, and the empty document is outside its
domain; the depth and token clauses are the parser's own limits
(`Parse.lean:30-35`), which the pipeline's ABI does not carry.

**The event capacity is not restated here.**  It is a conjunct of
`pipelineStaging`, so it arrives with this definition's first conjunct; the
binder below names the same ABI slot and the same slot value, since
`pipelineEvCapacity`/`pipelineNevSlot` read the `evcap` argument and the `nev`
cursor slot that the staging binds.  Stating the inequality here as well would be
a second spelling of one fact, so a proof that needs it reads it off the staging.
-/
def pipelineSpecPre (base : Nat) (args : List Value) (mem : Mem)
    (_next : Nat) : Prop :=
  pipelineStaging base args mem ∧
  ∃ (bs : List UInt8) (nev0 evcap nev : Nat),
    pipelineDocLength args = some bs.length ∧
    pipelineEvCapacity args = some evcap ∧
    pipelineNevSlot args = some nev ∧
    readBytes mem base bs.length = some bs ∧
    readBytes mem nev 8 = some (wordBytes 8 nev0) ∧
    (∀ e : ParseError,
      parseBytes Limits.default (ByteString.literal bs) = .error e →
        e ≠ .depthExceeded ∧ e ≠ .outOfCapacity)

/-! ### The post -/

/-- The reference parser's predicate, at `LeanLLVM.JSON.Limits.default`.

On return the word is the ABI's verdict and the caller observes, at its own
buffers, the parser's answers: acceptance exactly where `parseBytes` accepts, the
accepted value and the tape's validity, the event stream's record stream naming
the parser's tokens, the first error offset at the stage that owns the refusal,
and no byte outside the extent the run wrote moved.  The semantic content is
stated here and deliberately not in `Γ_pipeline_units`: that record's post is
about the buffers, and this one is about the parser
(`JsonPipelineContract`'s docstring). -/
def Sigma_pipeline (eventRel : EventStreamRel) (base : Nat) (args : List Value)
    (mem : Mem) (_next : Nat) (o : Outcome) : Prop :=
  match o with
  | .ub => False
  | .ret (some (.int 64 verdict)) m =>
      match args with
      | [.ptr _, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 epcap,
         .ptr nk, .ptr xp, .int 64 xpcap, .ptr nxp, .ptr xcarry, .ptr dst,
         .int 64 dstcap, .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err,
         .int 64 _] =>
          ∃ (bs : List UInt8) (nk' nxp' ndst' nev' : Nat),
            n.toNat = bs.length ∧
            readBytes mem base n.toNat = some bs ∧
            -- the four cursors at the boundary, as the body's post reads them
            readBytes m nk 8 = some (wordBytes 8 nk') ∧
            readBytes m nxp 8 = some (wordBytes 8 nxp') ∧
            readBytes m ndst 8 = some (wordBytes 8 ndst') ∧
            readBytes m nev 8 = some (wordBytes 8 nev') ∧
            -- the return word is the ABI's verdict (`pipeline.h:55-57`)
            (verdict = 0 ∨ verdict = 1) ∧
            -- acceptance is `.ok` exactly when the parser accepts
            (verdict = 1 ↔
              ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t) ∧
            -- on acceptance: the parser's value, the tape's validity, and the
            -- event stream naming the parser's tokens
            (verdict = 1 →
              ∃ (t : Tape) (v : LeanLLVM.JSON.Value) (arena evs : List UInt8),
                parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
                t.input = ByteString.literal bs ∧
                decodeTape t = some v ∧
                readBytes m dst ndst' = some arena ∧
                readBytes m ev nev' = some evs ∧
                eventRel bs arena evs t.tokens ∧
                spansWellFormed t = true ∧
                ValidDocument (ByteString.literal bs) v) ∧
            -- on refusal: the first error offset, at the stage that owns it
            (verdict = 0 →
              ∃ e : Nat,
                readBytes m err 8 = some (wordBytes 8 e) ∧
                RefusalOffset bs e) ∧
            -- every byte outside the extent the run wrote is unchanged, so the
            -- document at `base` is not modified
            UnchangedOutside mem m
              [(sc, 24), (mk, 48), (entw, 8), (ep, 4 * (nk' + 8)), (nk, 8),
               (xp, 4 * (nxp' + 8)), (nxp, 8), (xcarry, 16),
               (dst, ndst' + 64), (ndst, 8), (ev, nev'), (nev, 8), (err, 8)]
      | _ => False
  | _ => False

/-- Undefined behaviour is refused by the post, not by prose: `Sigma_pipeline` is
`False` at `.ub`, and `Satisfies`'s completion conjunct plus
`runFuel_outcome_unique` is what excludes it (`Refinement.lean:194-215`). -/
theorem Sigma_pipeline_ub_false (eventRel : EventStreamRel) (base : Nat)
    (args : List Value) (mem : Mem) (next : Nat) :
    ¬ Sigma_pipeline eventRel base args mem next .ub :=
  fun h => h

/-! ### The record -/

/-- The pipeline's specification record: the body's staging and fuel, read by
name, with the parser's predicate as the post.  D2 obtains
`Satisfies pipelineCalls pipelineBody (Γ_pipeline eventRel base)` from
`Γ_pipeline_units`'s instance and `Satisfies.mono`, whose post hypothesis is the
finalisation lemma; `eventRel` is then C95's relation. -/
def Γ_pipeline (eventRel : EventStreamRel) (base : Nat) : MemContract where
  budget := pipelineBudget
  pre := pipelineSpecPre base
  post := Sigma_pipeline eventRel base

/-! ### Sanity checks on the statement's data and its ABI projections -/

-- The position-free refusal is the only one without a `some`.
#guard rejectPos .byteOrderMark = none
#guard rejectPos (.unexpectedByte 3 93) = some 3
#guard rejectPos (.badUTF8 1) = some 1

-- Each projection lands on its own field; an unshaped list yields `none`.
-- The list is the contract module's read-set guard shape
-- (`JsonPipelineContract.lean`'s `#guard`), the twenty `pipeline.h` arguments.
#guard pipelineDocLength [.ptr 0, .int 64 7, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0] = some 7
#guard pipelineEvCapacity [.ptr 0, .int 64 7, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0] = some 4096
#guard pipelineNevSlot [.ptr 0, .int 64 7, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0] = some 240
#guard pipelineDocLength [] = none
#guard pipelineEvCapacity [] = none
#guard pipelineNevSlot [] = none

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.pipelineDocLength' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineDocLength

/-- info: 'LeanLLVM.Vellum.pipelineEvCapacity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineEvCapacity

/-- info: 'LeanLLVM.Vellum.pipelineNevSlot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineNevSlot

/-- info: 'LeanLLVM.Vellum.rejectPos' does not depend on any axioms -/
#guard_msgs in
#print axioms rejectPos

/-- info: 'LeanLLVM.Vellum.RefusalOffset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RefusalOffset

/-- info: 'LeanLLVM.Vellum.pipelineSpecPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineSpecPre

/-- info: 'LeanLLVM.Vellum.Sigma_pipeline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sigma_pipeline

/-- info: 'LeanLLVM.Vellum.Γ_pipeline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Γ_pipeline

/-- info: 'LeanLLVM.Vellum.Sigma_pipeline_ub_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sigma_pipeline_ub_false

end LeanLLVM.Vellum
