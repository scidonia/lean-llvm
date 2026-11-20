/-
# The depth-zero closing brace's refusal offset, at the parser

The refusing routes are produced (`JsonStage2WalkDispatchRefusalsOfStaging`'s arms,
`JsonStage2WalkFlushPost`'s flush word); what their refusal row still owes is the
parser-side statement that the parser's own refusal at such a document carries the
position the route stores (`ParserRows`' third conjunct, `RefusalOffset` in
`JsonPipelineSpec`).  `JsonStage2WalkRefusalOffsetBracket` settles that row for the
closing bracket with nothing open; this module settles it for the closing brace.

## The route and its stored offset

`HcontArm.closeBraceZero` and `LastEntryArm.closeBraceZero` are the two producers of
one arm: `NodeBlock21 → NodeBlock19 → NodeBlock17 → LeafBlock15 → if.then53.i →
if.then56.i → if.then` (`closeBraceZero_at`'s six links).  The first four links are
the brace's own pivots — `%Pivot22` separates it from the comma's paths, `%Pivot20`
from the colon's and the containers', `%Pivot18` and `%SwitchLeaf16` from the
bracket's, which take `NodeBlock11 → LeafBlock9` — and the last two are shared with
the bracket arm because neither the depth test nor the offset store reads the byte.
`if.then53.i` tests the depth register and takes its zero arm (`C.sp = 0`), and
`if.then56.i` stores the entry's position at `%e + 8`, then jumps to the refusal
copy (`refuseStep₆`, whose carry is `{ C with block := "if.then", eoff := j,
refusal := true }`).  The word the store writes is `%idxprom.i`'s, and `WalkInv.idx_reg`
carries that register as `entryPos G C.k` — the position of the brace entry in the
document.  So the route's refusal offset is `entryPos G C.k`, and that is the
position the copy loads (`refuseSegment_word_of_store`) and the caller reads.  The
arm's producer supplies exactly that index (`hcontArm_closeBraceZero_of_staging`'s
`j`), not a number chosen at the dispatch.

## The parser's answer at such a document

The document shape this row reads is the one that makes the brace the parser's next
token: the bytes up to the brace are JSON whitespace, and the brace itself is
`0x7D`.  `spaceRun_literal_append_closeBrace` reads the whitespace prefix's run as its
length (`spaceRun_cons` at each prefix byte, the brace byte ending the run), so
`skipFrom` from `0` stops at the brace (`skipFrom_literal_append_closeBrace`).
`parseValue` there finds `0x7D`, which is not an opener, not the string opener, none
of the three literals, and not a number's first byte, so it refuses
`unexpectedByte pre.length 0x7D` (`parseValue_of_getElem?_closeBrace`); the
byte-order-mark test precedes the syntax test and fails, because the document's first
byte is a whitespace byte or the brace itself, neither of which is `0xEF`
(`take3_ne_bom_append_closeBrace`).  `parseBytes` therefore returns
`.error (.invalid (.unexpectedByte pre.length 0x7D))`
(`parseBytes_spacePrefix_closeBrace`), and `refusalOffset_spacePrefix_closeBrace`
reads `rejectPos` at that constructor into `RefusalOffset`.

`walkRefusalOffset_brace` states the row at the geometry: with the document's prefix
as whitespace and the brace at `entryPos G C.k`, the parser's refusal is the offset
the arm stored.

## The UTF-8 premise, and why it is the route's

`RefusalOffset` splits on the stage that owns the refusal: a UTF-8-invalid document
refuses at its end, because the stage reports invalidity without a position
(`stage2.h:60-62`), and only a UTF-8-valid document's offset is the parser's.  The
walk runs after that stage, so its route is the valid-prefix branch; the geometry
does not carry the stage's verdict, so the premise is stated here rather than derived.
On the other branch the clause is vacuous (`refusalOffset_spacePrefix_closeBrace`'s
second conjunct is discharged by the premise).

## Why the document hypothesis, and not the geometry alone

The staging's `entries` record the entry stream's positions, not its bytes: `inside`
bounds each position by the document's length and `order` orders them, and nothing in
`WalkGeom` ties `G.bs` at a position to a byte.  That the staged entries are the
emitter's lanes is the entry stage's composition (`JsonEntSpec` and the stage-1
emitter), outside this tree.  So the document's content is this route's parser-side
hypothesis, exactly as the flush route's whitespace-only document is; the offset is not
weakened by it, because the statement pins it at the brace's own position — what
`if.then56.i` stored.

Two levels produce the arm and one document shape is stated.  A whitespace prefix has
no entry at the emitter's own naming, so the brace is the stream's first entry and the
shape is the last-entry producer's selector (`¬ (C.k + 1 < G.nep)` at `C.k = 0`); the
continuing level stores the same register, so the row is stated at `entryPos G C.k`
and not at a level — the statement never reads the count.

The brace's pivots differ from the bracket's, but the two byte-agnostic facts this
module leans on are the bracket module's: `ne_ef_of_isSpaceB` and
`take3_ne_bom_of_getElem?_zero` are about the mark's `0xEF`, not about either
delimiter, so they are imported rather than restated.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffsetBracket

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The whitespace prefix before the brace

The parser's white-space skip is the definitional `spaceRun` over the carrier, whose
cons equation is `spaceRun_cons`.  A prefix of whitespace bytes contributes one to the
run per byte, and the brace byte ends it. -/

/-- **The run over a whitespace prefix, ended by the brace, is its length.**  Each
prefix byte is whitespace (`spaceRun_cons`'s true arm), and the brace is not
(`IsSpaceB 0x7D = false`), so the run stops there. -/
theorem spaceRun_literal_append_closeBrace (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    spaceRun (ByteString.literal (pre ++ 0x7D :: rest)) = pre.length := by
  induction pre with
  | nil =>
      rw [List.nil_append, ByteString.literal_cons, spaceRun_cons]
      rfl
  | cons b pre ih =>
      rw [List.cons_append, ByteString.literal_cons, spaceRun_cons,
        ite_eq_left (hws b (by simp)), ih (fun x hx => hws x (by simp [hx]))]
      simp

/-- **The parser's skip stops at the brace.**  `skipFrom` from `0` is the run over
the document, which is the prefix's length. -/
theorem skipFrom_literal_append_closeBrace (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    skipFrom (ByteString.literal (pre ++ 0x7D :: rest)) 0 = pre.length := by
  rw [skipFrom_def, ByteString.drop_zero,
    spaceRun_literal_append_closeBrace pre rest hws, Nat.zero_add]

/-- **The byte at the prefix's end is the brace.**  The lookup skips the prefix and
reads the head of the remaining list. -/
theorem getElem?_append_closeBrace (pre rest : List UInt8) :
    (pre ++ 0x7D :: rest)[pre.length]? = some 0x7D := by
  rw [List.getElem?_append, ite_eq_right (Nat.lt_irrefl _), Nat.sub_self]
  rfl

/-! ### The mark test's failure

`parseBytes` tests the three mark bytes before it parses, so its answer at this
document needs the test to fail.  A whitespace byte is not `0xEF`, and neither is the
brace; both facts are the bracket module's, stated over the byte rather than the
delimiter. -/

/-- **The mark test fails at a whitespace prefix and a brace.**  The first byte is a
whitespace byte (the prefix is non-empty) or the brace (it is empty), and neither is
the mark's `0xEF`. -/
theorem take3_ne_bom_append_closeBrace (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    (ByteString.literal (pre ++ 0x7D :: rest)).take 3
      ≠ ByteString.literal [0xEF, 0xBB, 0xBF] := by
  cases pre with
  | nil => exact take3_ne_bom_of_getElem?_zero (b := 0x7D) (by simp) (by decide)
  | cons b pre =>
      exact take3_ne_bom_of_getElem?_zero (b := b) (by simp)
        (ne_ef_of_isSpaceB (hws b (by simp)))

/-! ### The value parser at the brace

`parseValue`'s first test is `bs[i]?`; the arm it takes is the last one, the default
that refuses a byte which is neither a container, a string opener, a literal's first
byte, nor a number's. -/

/-- **The value parser refuses `0x7D` at its own position.**  `0x7D` is not `0x5B`,
`0x7B`, `0x22`, `0x74`, `0x66` or `0x6E`, and it is not `-` or a digit, so the
`match` reaches its last arm and reports the byte it read. -/
theorem parseValue_of_getElem?_closeBrace {bs : Bytes} {i depth : Nat}
    (h : bs[i]? = some 0x7D) :
    parseValue bs i depth = .fail (.invalid (.unexpectedByte i 0x7D)) := by
  rw [parseValue.eq_def]
  split
  all_goals simp_all [IsDigitB]

/-! ### The parser's refusal at the document -/

/-- **The parser refuses a whitespace-prefixed brace document at the brace.**  The
input bound is met and the mark test fails, so `parseBytes` enters `parseValue` at the
skipped-to cursor — the brace — where the value parser refuses. -/
theorem parseBytes_spacePrefix_closeBrace {pre rest : List UInt8}
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbound : (pre ++ 0x7D :: rest).length ≤ Limits.default.maxInput) :
    parseBytes Limits.default (ByteString.literal (pre ++ 0x7D :: rest)) =
      .error (.invalid (.unexpectedByte pre.length 0x7D)) := by
  have hskip := skipFrom_literal_append_closeBrace pre rest hws
  have hfail := parseValue_of_getElem?_closeBrace
    (bs := ByteString.literal (pre ++ 0x7D :: rest))
    (i := skipFrom (ByteString.literal (pre ++ 0x7D :: rest)) 0)
    (depth := Limits.default.maxDepth)
    (by rw [hskip, ByteString.getElem?_literal]; exact getElem?_append_closeBrace pre rest)
  unfold parseBytes
  rw [ite_eq_right (by rw [literal_length]; omega),
    ite_eq_right (take3_ne_bom_append_closeBrace pre rest hws)]
  split
  · rename_i p hp
    rw [hfail] at hp
    cases hp
  · rename_i e hp
    have he : e = .invalid
        (.unexpectedByte (skipFrom (ByteString.literal (pre ++ 0x7D :: rest)) 0) 0x7D) := by
      rw [hp] at hfail
      injection hfail with h
    rw [he, hskip]

/-! ### The refusal offset -/

/-- **The brace route's refusal offset is the parser's.**  At a document whose
prefix is whitespace and whose next byte is `0x7D`, on the walk's UTF-8-valid branch,
every refusal the parser reports is `.unexpectedByte` at the brace — or the
byte-order mark, which carries no position and which this document cannot open with —
so `RefusalOffset` holds at the brace's position. -/
theorem refusalOffset_spacePrefix_closeBrace {pre rest : List UInt8}
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbound : (pre ++ 0x7D :: rest).length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window (pre ++ 0x7D :: rest)
      (pre ++ 0x7D :: rest).length (pipelineBlocks (pre ++ 0x7D :: rest).length))) :
    RefusalOffset (pre ++ 0x7D :: rest) pre.length := by
  have hparse := parseBytes_spacePrefix_closeBrace hws hbound
  unfold RefusalOffset
  dsimp only
  refine ⟨?_, fun hnot => absurd hutf8 hnot⟩
  intro _ r hr
  rw [hparse] at hr
  have hr' : r = .unexpectedByte pre.length 0x7D := by
    injection hr with h1
    injection h1 with h2
    exact h2.symm
  subst hr'
  simp [rejectPos]

/-- **The brace route's offset, at the geometry's document.**  The arm's store writes
`%idxprom.i`'s word, which `WalkInv.idx_reg` carries as `entryPos G C.k`; the document's
prefix is the whitespace the parser skips, so the parser's refusal is that position.
The document's content and the stage's validity are stated here, for the reasons the
module gives. -/
theorem walkRefusalOffset_brace {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {pre rest : List UInt8} (hbs : G.bs = pre ++ 0x7D :: rest)
    (hpos : pre.length = entryPos G C.k)
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbound : G.bs.length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window G.bs G.bs.length (pipelineBlocks G.bs.length))) :
    RefusalOffset G.bs (entryPos G C.k) := by
  rw [← hpos]
  rw [hbs] at hbound hutf8 ⊢
  exact refusalOffset_spacePrefix_closeBrace hws hbound hutf8

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.spaceRun_literal_append_closeBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spaceRun_literal_append_closeBrace

/-- info: 'LeanLLVM.Refinement.skipFrom_literal_append_closeBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms skipFrom_literal_append_closeBrace

/-- info: 'LeanLLVM.Refinement.getElem?_append_closeBrace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getElem?_append_closeBrace

/-- info: 'LeanLLVM.Refinement.take3_ne_bom_append_closeBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take3_ne_bom_append_closeBrace

/-- info: 'LeanLLVM.Refinement.parseValue_of_getElem?_closeBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseValue_of_getElem?_closeBrace

/-- info: 'LeanLLVM.Refinement.parseBytes_spacePrefix_closeBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseBytes_spacePrefix_closeBrace

/-- info: 'LeanLLVM.Refinement.refusalOffset_spacePrefix_closeBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_spacePrefix_closeBrace

/-- info: 'LeanLLVM.Refinement.walkRefusalOffset_brace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkRefusalOffset_brace

end LeanLLVM.Refinement
