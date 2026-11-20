/-
# The depth-zero closing bracket's refusal offset, at the parser

The refusing routes are produced (`JsonStage2WalkDispatchRefusalsOfStaging`'s arms,
`JsonStage2WalkFlushPost`'s flush word); what their refusal row still owes is the
parser-side statement that the parser's own refusal at such a document carries the
position the route stores (`ParserRows`' third conjunct, `RefusalOffset` in
`JsonPipelineSpec`).  This module settles that row for a second route: the closing
bracket with nothing open.

## The route and its stored offset

`HcontArm.closeBracketZero` and `LastEntryArm.closingZero` are the two producers of
one arm: `NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock9 → if.then53.i →
if.then56.i → if.then` (`bracketRefuse_at`'s six links).  `if.then53.i` tests the
depth register and takes its zero arm (`C.sp = 0`), and `if.then56.i` stores the
entry's position at `%e + 8`, then jumps to the refusal copy (`refuseStep₆`, whose
carry is `{ C with block := "if.then", eoff := j, refusal := true }`).  The word the
store writes is `%idxprom.i`'s, and `WalkInv.idx_reg` carries that register as
`entryPos G C.k` — the position of the bracket entry in the document.  So the route's
refusal offset is `entryPos G C.k`, and that is the position the copy loads
(`refuseSegment_word_of_store`) and the caller reads.  The arm's producer supplies
exactly that index (`hcontArm_closeBracketZero_of_staging`'s `j`), not a number chosen
at the dispatch.

## The parser's answer at such a document

The document shape this row reads is the one that makes the bracket the parser's next
token: the bytes up to the bracket are JSON whitespace, and the bracket itself is
`0x5D`.  `spaceRun_literal_append_closeBracket` reads the whitespace prefix's run as
its length (`spaceRun_cons` at each prefix byte, the bracket byte ending the run), so
`skipFrom` from `0` stops at the bracket
(`skipFrom_literal_append_closeBracket`).  `parseValue` there finds `0x5D`, which is
not an opener, not the string opener, none of the three literals, and not a number's
first byte, so it refuses `unexpectedByte pre.length 0x5D`
(`parseValue_of_getElem?_closeBracket`); the byte-order-mark test precedes the syntax
test and fails, because the document's first byte is a whitespace byte or the bracket
itself, neither of which is `0xEF`
(`take3_ne_bom_append_closeBracket`).  `parseBytes` therefore returns
`.error (.invalid (.unexpectedByte pre.length 0x5D))`
(`parseBytes_spacePrefix_closeBracket`), and `refusalOffset_spacePrefix_closeBracket`
reads `rejectPos` at that constructor into `RefusalOffset`.

`walkRefusalOffset_bracket` states the row at the geometry: with the document's prefix
as whitespace and the bracket at `entryPos G C.k`, the parser's refusal is the offset
the arm stored.

## The UTF-8 premise, and why it is the route's

`RefusalOffset` splits on the stage that owns the refusal: a UTF-8-invalid document
refuses at its end, because the stage reports invalidity without a position
(`stage2.h:60-62`), and only a UTF-8-valid document's offset is the parser's.  The
walk runs after that stage, so its route is the valid-prefix branch; the geometry
does not carry the stage's verdict, so the premise is stated here rather than derived.
On the other branch the clause is vacuous (`refusalOffset_spacePrefix_closeBracket`'s
second conjunct is discharged by the premise).

## Why the document hypothesis, and not the geometry alone

The staging's `entries` record the entry stream's positions, not its bytes: `inside`
bounds each position by the document's length and `order` orders them, and nothing in
`WalkGeom` ties `G.bs` at a position to a byte.  That the staged entries are the
emitter's lanes is the entry stage's composition (`JsonEntSpec` and the stage-1
emitter), outside this tree.  So the document's content is this route's parser-side
hypothesis, exactly as the flush route's whitespace-only document is; the offset is not
weakened by it, because the statement pins it at the bracket's own position — what
`if.then56.i` stored.

Two levels produce the arm and one document shape is stated.  A whitespace prefix has
no entry at the emitter's own naming, so the bracket is the stream's first entry and
the shape is the last-entry producer's selector (`¬ (C.k + 1 < G.nep)` at
`C.k = 0`); the continuing level stores the same register, so the row is stated at
`entryPos G C.k` and not at a level — the statement never reads the count.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffset

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The whitespace prefix before the bracket

The parser's white-space skip is the definitional `spaceRun` over the carrier, whose
cons equation is `spaceRun_cons`.  A prefix of whitespace bytes contributes one to the
run per byte, and the bracket byte ends it. -/

/-- **The run over a whitespace prefix, ended by the bracket, is its length.**  Each
prefix byte is whitespace (`spaceRun_cons`'s true arm), and the bracket is not
(`IsSpaceB 0x5D = false`), so the run stops there. -/
theorem spaceRun_literal_append_closeBracket (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    spaceRun (ByteString.literal (pre ++ 0x5D :: rest)) = pre.length := by
  induction pre with
  | nil =>
      rw [List.nil_append, ByteString.literal_cons, spaceRun_cons]
      rfl
  | cons b pre ih =>
      rw [List.cons_append, ByteString.literal_cons, spaceRun_cons,
        ite_eq_left (hws b (by simp)), ih (fun x hx => hws x (by simp [hx]))]
      simp

/-- **The parser's skip stops at the bracket.**  `skipFrom` from `0` is the run over
the document, which is the prefix's length. -/
theorem skipFrom_literal_append_closeBracket (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    skipFrom (ByteString.literal (pre ++ 0x5D :: rest)) 0 = pre.length := by
  rw [skipFrom_def, ByteString.drop_zero,
    spaceRun_literal_append_closeBracket pre rest hws, Nat.zero_add]

/-- **The byte at the prefix's end is the bracket.**  The lookup skips the prefix and
reads the head of the remaining list. -/
theorem getElem?_append_closeBracket (pre rest : List UInt8) :
    (pre ++ 0x5D :: rest)[pre.length]? = some 0x5D := by
  rw [List.getElem?_append, ite_eq_right (Nat.lt_irrefl _), Nat.sub_self]
  rfl

/-! ### The mark test's failure

`parseBytes` tests the three mark bytes before it parses, so its answer at this
document needs the test to fail.  A whitespace byte is not `0xEF`, and neither is the
bracket. -/

/-- **No JSON whitespace byte is `0xEF`.**  The set is the four bytes of RFC 8259
§2's `ws` production. -/
theorem ne_ef_of_isSpaceB {b : UInt8} (h : IsSpaceB b = true) : b ≠ 0xEF := by
  unfold IsSpaceB at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rintro rfl
  rcases h with h | h | h | h
  all_goals exact absurd h (by decide)

/-- **A document whose first byte is not `0xEF` does not open with the mark.**  The
take's byte at index `0` is the document's, so a take that begins with the mark's
`0xEF` would make the document begin with it too. -/
theorem take3_ne_bom_of_getElem?_zero {bs : List UInt8} {b : UInt8}
    (h0 : bs[0]? = some b) (hb : b ≠ 0xEF) :
    (ByteString.literal bs).take 3 ≠ ByteString.literal [0xEF, 0xBB, 0xBF] := by
  intro hbom
  have h : ((ByteString.literal bs).take 3)[0]? = some 0xEF := by
    rw [hbom, ByteString.getElem?_literal]
    simp
  rw [ByteString.getElem?_take, ite_eq_left (by decide : 0 < 3),
    ByteString.getElem?_literal] at h
  rw [h0] at h
  exact hb (Option.some.inj h)

/-- **The mark test fails at a whitespace prefix and a bracket.**  The first byte is a
whitespace byte (the prefix is non-empty) or the bracket (it is empty), and neither is
the mark's `0xEF`. -/
theorem take3_ne_bom_append_closeBracket (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    (ByteString.literal (pre ++ 0x5D :: rest)).take 3
      ≠ ByteString.literal [0xEF, 0xBB, 0xBF] := by
  cases pre with
  | nil => exact take3_ne_bom_of_getElem?_zero (b := 0x5D) (by simp) (by decide)
  | cons b pre =>
      exact take3_ne_bom_of_getElem?_zero (b := b) (by simp)
        (ne_ef_of_isSpaceB (hws b (by simp)))

/-! ### The value parser at the bracket

`parseValue`'s first test is `bs[i]?`; the arm it takes is the last one, the default
that refuses a byte which is neither a container, a string opener, a literal's first
byte, nor a number's. -/

/-- **The value parser refuses `0x5D` at its own position.**  `0x5D` is not `0x5B`,
`0x7B`, `0x22`, `0x74`, `0x66` or `0x6E`, and it is not `-` or a digit, so the
`match` reaches its last arm and reports the byte it read. -/
theorem parseValue_of_getElem?_closeBracket {bs : Bytes} {i depth : Nat}
    (h : bs[i]? = some 0x5D) :
    parseValue bs i depth = .fail (.invalid (.unexpectedByte i 0x5D)) := by
  rw [parseValue.eq_def]
  split
  all_goals simp_all [IsDigitB]

/-! ### The parser's refusal at the document -/

/-- **The parser refuses a whitespace-prefixed bracket document at the bracket.**  The
input bound is met and the mark test fails, so `parseBytes` enters `parseValue` at the
skipped-to cursor — the bracket — where the value parser refuses. -/
theorem parseBytes_spacePrefix_closeBracket {pre rest : List UInt8}
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbound : (pre ++ 0x5D :: rest).length ≤ Limits.default.maxInput) :
    parseBytes Limits.default (ByteString.literal (pre ++ 0x5D :: rest)) =
      .error (.invalid (.unexpectedByte pre.length 0x5D)) := by
  have hskip := skipFrom_literal_append_closeBracket pre rest hws
  have hfail := parseValue_of_getElem?_closeBracket
    (bs := ByteString.literal (pre ++ 0x5D :: rest))
    (i := skipFrom (ByteString.literal (pre ++ 0x5D :: rest)) 0)
    (depth := Limits.default.maxDepth)
    (by rw [hskip, ByteString.getElem?_literal]; exact getElem?_append_closeBracket pre rest)
  unfold parseBytes
  rw [ite_eq_right (by rw [literal_length]; omega),
    ite_eq_right (take3_ne_bom_append_closeBracket pre rest hws)]
  split
  · rename_i p hp
    rw [hfail] at hp
    cases hp
  · rename_i e hp
    have he : e = .invalid
        (.unexpectedByte (skipFrom (ByteString.literal (pre ++ 0x5D :: rest)) 0) 0x5D) := by
      rw [hp] at hfail
      injection hfail with h
    rw [he, hskip]

/-! ### The refusal offset -/

/-- **The bracket route's refusal offset is the parser's.**  At a document whose
prefix is whitespace and whose next byte is `0x5D`, on the walk's UTF-8-valid branch,
every refusal the parser reports is `.unexpectedByte` at the bracket — or the
byte-order mark, which carries no position and which this document cannot open with —
so `RefusalOffset` holds at the bracket's position. -/
theorem refusalOffset_spacePrefix_closeBracket {pre rest : List UInt8}
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbound : (pre ++ 0x5D :: rest).length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window (pre ++ 0x5D :: rest)
      (pre ++ 0x5D :: rest).length (pipelineBlocks (pre ++ 0x5D :: rest).length))) :
    RefusalOffset (pre ++ 0x5D :: rest) pre.length := by
  have hparse := parseBytes_spacePrefix_closeBracket hws hbound
  unfold RefusalOffset
  dsimp only
  refine ⟨?_, fun hnot => absurd hutf8 hnot⟩
  intro _ r hr
  rw [hparse] at hr
  have hr' : r = .unexpectedByte pre.length 0x5D := by
    injection hr with h1
    injection h1 with h2
    exact h2.symm
  subst hr'
  simp [rejectPos]

/-- **The bracket route's offset, at the geometry's document.**  The arm's store writes
`%idxprom.i`'s word, which `WalkInv.idx_reg` carries as `entryPos G C.k`; the document's
prefix is the whitespace the parser skips, so the parser's refusal is that position.
The document's content and the stage's validity are stated here, for the reasons the
module gives. -/
theorem walkRefusalOffset_bracket {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {pre rest : List UInt8} (hbs : G.bs = pre ++ 0x5D :: rest)
    (hpos : pre.length = entryPos G C.k)
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbound : G.bs.length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window G.bs G.bs.length (pipelineBlocks G.bs.length))) :
    RefusalOffset G.bs (entryPos G C.k) := by
  rw [← hpos]
  rw [hbs] at hbound hutf8 ⊢
  exact refusalOffset_spacePrefix_closeBracket hws hbound hutf8

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.spaceRun_literal_append_closeBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spaceRun_literal_append_closeBracket

/-- info: 'LeanLLVM.Refinement.skipFrom_literal_append_closeBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms skipFrom_literal_append_closeBracket

/-- info: 'LeanLLVM.Refinement.getElem?_append_closeBracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getElem?_append_closeBracket

/-- info: 'LeanLLVM.Refinement.ne_ef_of_isSpaceB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ne_ef_of_isSpaceB

/-- info: 'LeanLLVM.Refinement.take3_ne_bom_of_getElem?_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take3_ne_bom_of_getElem?_zero

/-- info: 'LeanLLVM.Refinement.take3_ne_bom_append_closeBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take3_ne_bom_append_closeBracket

/-- info: 'LeanLLVM.Refinement.parseValue_of_getElem?_closeBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseValue_of_getElem?_closeBracket

/-- info: 'LeanLLVM.Refinement.parseBytes_spacePrefix_closeBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseBytes_spacePrefix_closeBracket

/-- info: 'LeanLLVM.Refinement.refusalOffset_spacePrefix_closeBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_spacePrefix_closeBracket

/-- info: 'LeanLLVM.Refinement.walkRefusalOffset_bracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkRefusalOffset_bracket

end LeanLLVM.Refinement
