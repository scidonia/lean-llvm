/-
# The flush route's refusal offset, at the parser

The refusing routes are produced (`JsonStage2WalkDispatchRefusalsOfStaging`'s arms,
`JsonStage2WalkFlushPost`'s flush word); what their refusal row still owes is the
parser-side statement that the parser's own refusal at such a document carries the
position the route stores (`ParserRows`' third conjunct, `RefusalOffset` in
`JsonPipelineSpec`).  This module settles that row for one route: the flush arm.

## The route and its stored offset

At `G.nep = 0` the entry block's test takes its zero arm and the flush block runs
(`walkFlushAt_of_staging`'s `hzero`); that block stores the document's length in the
error record's offset field, and the refusal copy writes the same word to the
caller's `*err` (`walkFlushMemAt`'s offset store and its last write).  So the flush
route's refusal offset is `G.n`, and the row the caller reads is `RefusalOffset G.bs
G.n`.

## The parser's answer at that document

`parseBytes_allSpace` is the parser's own fact for the document the empty entry
stream stands for: a document whose bytes are all JSON whitespace, at a length
inside the input bound.  The parser skips the whole input and refuses at
`skipFrom bs 0 = bs.length` with `.unexpectedEnd`, whose `rejectPos` is the
document's end; the one answer that precedes the syntax test, the byte-order mark,
carries no position (`rejectPos .byteOrderMark = none`) and leaves the clause
vacuous.  `refusalOffset_allSpace` reads the two into `RefusalOffset bs bs.length`,
and `walkRefusalOffset_flush` states it at the geometry as `RefusalOffset G.bs G.n`
— `G.n` is `G.bs.length` by the staging's own read (`readBytes_length`).

## Why the document hypothesis, and not `G.nep = 0`

The staging names an entry at every unescaped quote, at every delimiter outside a
string, and at every scalar-run start (`JsonEntSpec.entryMask64`), so the stream the
flush route consumes at `G.nep = 0` is the document with none of those bytes — the
whitespace-only document.  That the staged `G.ent` *is* the emitter's lanes is the
entry route's composition (`JsonEntSpec`'s masks and the stage-1 emitter), which is
outside this tree; the geometry itself records only that the positions are ordered
and inside the document, so `G.nep = 0` alone constrains no byte of `G.bs`.  The
document's content is therefore stated as this route's parser-side hypothesis rather
than derived from `WalkGeom`.  The offset is not weakened by doing so: the statement
pins it at the document's end, which is what the flush block stored.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkScopeGeom
import LeanLLVM.Refinement.JsonPipelineSpec

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### A whitespace-only document's run

The parser's white-space skip is the definitional `spaceRun` over the carrier.  At a
list every byte of which is whitespace, the run is the list's length, and the skip
from `0` is that length. -/

/-- **The whitespace run of a whitespace-only document is its length.** -/
theorem spaceRun_literal_of_allSpace (l : List UInt8)
    (hws : ∀ b ∈ l, IsSpaceB b = true) :
    spaceRun (ByteString.literal l) = l.length := by
  induction l with
  | nil =>
      rw [show ByteString.literal ([] : List UInt8) = ByteString.empty from rfl,
        spaceRun_empty]
      simp
  | cons b rest ih =>
      have hb : IsSpaceB b = true := hws b (by simp)
      rw [ByteString.literal_cons, spaceRun_cons, ite_eq_left hb,
        ih (fun x hx => hws x (by simp [hx]))]
      simp

/-- **The parser skips a whitespace-only document to its end.** -/
theorem skipFrom_literal_of_allSpace (l : List UInt8)
    (hws : ∀ b ∈ l, IsSpaceB b = true) :
    skipFrom (ByteString.literal l) 0 = l.length := by
  rw [skipFrom_def, ByteString.drop_zero, spaceRun_literal_of_allSpace l hws, Nat.zero_add]

/-! ### The parser at the end of its input -/

/-- **An exhausted cursor is `.unexpectedEnd` at that cursor.**  The value parser's
first test is `bs[i]?`; when it reads nothing there, the refusal is the position it
read at. -/
theorem parseValue_of_getElem?_none {bs : Bytes} {i : Nat} (depth : Nat)
    (h : bs[i]? = none) :
    parseValue bs i depth = .fail (.invalid (.unexpectedEnd i)) := by
  rw [parseValue.eq_def]
  split
  · rfl
  all_goals (exfalso; rename_i heq; rw [h] at heq; cases heq)

/-- A literal's length is its list's: the form the input-bound test reads. -/
theorem literal_length (bs : List UInt8) :
    (ByteString.literal bs).length = bs.length := by
  rw [ByteString.length_eq_size, ByteString.size_literal]

/-- **A whitespace-only document is not a byte-order mark.**  The mark's first byte
is `0xEF`, which is not whitespace, so a document every byte of which is whitespace
cannot begin with the three mark bytes. -/
theorem take3_ne_bom_of_allSpace {bs : List UInt8}
    (hws : ∀ b ∈ bs, IsSpaceB b = true) :
    (ByteString.literal bs).take 3 ≠ ByteString.literal [0xEF, 0xBB, 0xBF] := by
  intro hbom
  have h0 : (ByteString.literal bs)[0]? = some 0xEF := by
    have h : ((ByteString.literal bs).take 3)[0]? = some 0xEF := by
      rw [hbom, ByteString.getElem?_literal]
      simp
    rwa [ByteString.getElem?_take, ite_eq_left (by decide : 0 < 3)] at h
  have hmem : 0xEF ∈ bs := by
    rw [ByteString.getElem?_literal] at h0
    exact List.mem_of_getElem? h0
  have hsp := hws 0xEF hmem
  have hfalse : IsSpaceB 0xEF = false := by decide
  rw [hfalse] at hsp
  exact Bool.false_ne_true hsp

/-- **The byte-order mark's answer.**  The length test precedes it, so the bound is
the only premise the mark's branch needs. -/
theorem parseBytes_of_bom {bs : List UInt8}
    (hbound : bs.length ≤ Limits.default.maxInput)
    (hbom : (ByteString.literal bs).take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]) :
    parseBytes Limits.default (ByteString.literal bs) = .error (.invalid .byteOrderMark) := by
  unfold parseBytes
  rw [ite_eq_right (by rw [literal_length]; omega), ite_eq_left hbom]

/-- **The parser refuses a whitespace-only document at its end.**  The input bound
is met and the document is not a byte-order mark, so the value parser is entered at
the skipped-to cursor — the document's end — and refuses there. -/
theorem parseBytes_allSpace {bs : List UInt8}
    (hbound : bs.length ≤ Limits.default.maxInput)
    (hws : ∀ b ∈ bs, IsSpaceB b = true) :
    parseBytes Limits.default (ByteString.literal bs) =
      .error (.invalid (.unexpectedEnd bs.length)) := by
  unfold parseBytes
  rw [ite_eq_right (by rw [literal_length]; omega),
    ite_eq_right (take3_ne_bom_of_allSpace hws)]
  have hfail := parseValue_of_getElem?_none
    (bs := ByteString.literal bs) (i := skipFrom (ByteString.literal bs) 0)
    Limits.default.maxDepth
    (by rw [skipFrom_literal_of_allSpace bs hws]; simp)
  split
  · rename_i p hpv
    rw [hfail] at hpv
    cases hpv
  · rename_i e hpv
    have he : e = .invalid (.unexpectedEnd (skipFrom (ByteString.literal bs) 0)) := by
      rw [hpv] at hfail
      injection hfail with h
    rw [he, skipFrom_literal_of_allSpace bs hws]

/-! ### The refusal offset -/

/-- **The flush route's refusal offset is the parser's.**  At a whitespace-only
document inside the input bound, every refusal the parser reports is
`.unexpectedEnd` at the document's end — or the byte-order mark, which carries no
position — so `RefusalOffset bs bs.length` holds at the offset the flush block
stores. -/
theorem refusalOffset_allSpace {bs : List UInt8}
    (hbound : bs.length ≤ Limits.default.maxInput)
    (hws : ∀ b ∈ bs, IsSpaceB b = true) :
    RefusalOffset bs bs.length := by
  unfold RefusalOffset
  constructor
  · intro _ r hparse
    by_cases hbom : (ByteString.literal bs).take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]
    · rw [parseBytes_of_bom hbound hbom] at hparse
      have hr : r = .byteOrderMark := by
        injection hparse with h1
        injection h1 with h2
        exact h2.symm
      subst r
      simp [rejectPos]
    · rw [parseBytes_allSpace hbound hws] at hparse
      have hr : r = .unexpectedEnd bs.length := by
        injection hparse with h1
        injection h1 with h2
        exact h2.symm
      subst r
      simp [rejectPos]
  · intro _; rfl

/-- **The flush route's offset, at the geometry's document.**  The staging's read
names the document's length as `G.n` (`readBytes_length`), so the parser's answer at
the document is the route's stored offset.  `G.nep = 0` is the arm's guard
(`walkFlushAt_of_staging`); the document's content is stated here, for the reason
the module gives. -/
theorem walkRefusalOffset_flush {m0 : Mem} (G : WalkGeom m0)
    (hbound : G.bs.length ≤ Limits.default.maxInput)
    (hws : ∀ b ∈ G.bs, IsSpaceB b = true) :
    RefusalOffset G.bs G.n := by
  have hlen : G.bs.length = G.n := JsonEntrySteps.readBytes_length m0 G.b G.n G.doc
  rw [← hlen]
  exact refusalOffset_allSpace hbound hws

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.spaceRun_literal_of_allSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spaceRun_literal_of_allSpace

/-- info: 'LeanLLVM.Refinement.skipFrom_literal_of_allSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms skipFrom_literal_of_allSpace

/-- info: 'LeanLLVM.Refinement.parseValue_of_getElem?_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseValue_of_getElem?_none

/-- info: 'LeanLLVM.Refinement.parseBytes_allSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseBytes_allSpace

/-- info: 'LeanLLVM.Refinement.refusalOffset_allSpace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_allSpace

/-- info: 'LeanLLVM.Refinement.walkRefusalOffset_flush' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkRefusalOffset_flush

end LeanLLVM.Refinement
