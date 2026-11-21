/-
# The unterminated string's refusal offset, at the parser

The refusing routes are produced (`JsonStage2WalkDispatchRefusalsOfStaging`'s arms,
`JsonStage2WalkFlushPost`'s flush word); what their refusal row still owes is the
parser-side statement that the parser's own refusal at such a document carries the
position the route stores (`ParserRows`' third conjunct, `RefusalOffset` in
`JsonPipelineSpec`).  `JsonStage2WalkRefusalOffsetBracket` and
`JsonStage2WalkRefusalOffsetBrace` settle that row for the depth-zero closing
delimiters; this module settles it for the string opener with nothing left in the
entry stream.

## The route and its stored offset

`HcontArm.twoEntry`'s refusing sibling is the string opener at the last entry:
`NodeBlock21 → NodeBlock5 → LeafBlock → sw.bb202.i → if.then205.i → if.then`
(`quoteRefuse_at`'s five links).  The switch's two pivots and the leaf's equality
test reach `sw.bb202.i` at the quote's byte `34`; the count test there is false at
the last entry, and `if.then205.i` stores `%idxprom.i`'s word at `%e + 8` before
jumping to the refusal copy.  That register is `entryPos G C.k`
(`WalkInv.idx_reg`) — the position of the quote entry in the document — so the
route's refusal offset is `entryPos G C.k`, which is the opening quote itself.  The
parser reports `Reject.unterminatedString` at exactly that position
(`Parse.lean:138`, `rejectOf i .ended`), so the two sides name the same byte: the
opening quote, not the document's end.

## The parser's answer at such a document

The document shape this row reads is the whitespace prefix, then the opening quote,
then a body that never closes the string: `pre ++ 0x22 :: body`, where every body
byte is ASCII content (at least `0x20`, below `0x80`) other than the closing quote
and the escape introducer
(`IsQuoteBodyByte`).  `spaceRun_literal_append_quote` reads the whitespace prefix's
run as its length (`spaceRun_cons` at each prefix byte, the quote byte ending the
run), so `skipFrom` from `0` stops at the quote
(`skipFrom_literal_append_quote`).  `parseValue` there takes its string arm
(`parseValue_of_quote_ended` through `parseString_of_quote_ended` and
`parseKey_of_quote_ended`): `parseKey` matches the opening quote, and its
`scanCharsEnd bs (i + 1) 0` is `.error .ended`
(`scanCharsEnd_quote_body`), which `rejectOf i` maps to `.unterminatedString i`.
The scan reaches the end because each body byte is content: the ASCII branch of
`scanCharsFrom` accepts it (`scanCharsFrom_ascii`), the noncharacter test is false
on ASCII (`isNoncharacter_false_of_lt_80`), and the induction ends at
`scanCharsFrom_nil` (`scanCharsFrom_body_ended`).  The byte-order-mark test precedes
the syntax test and fails, because the document's first byte is a whitespace byte or
the quote itself, neither of which is `0xEF` (`take3_ne_bom_append_quote`).
`parseBytes` therefore returns
`.error (.invalid (.unterminatedString pre.length))`
(`parseBytes_spacePrefix_quote`), and `refusalOffset_quote` reads `rejectPos` at
that constructor into `RefusalOffset`.

`walkRefusalOffset_quote` states the row at the geometry: with the document's
prefix as whitespace and the opening quote at `entryPos G C.k`, the parser's refusal
is the offset the arm stored.

## Why a body of ASCII content

A string is unterminated when its body contains no closing quote, but a control
byte, a malformed escape, or invalid UTF-8 would make the scan refuse for that
reason instead of `.ended`; the row's reject is `.unterminatedString`, so the body's
content is part of the hypothesis, as the bracket's and brace's document content is.
`IsQuoteBodyByte` is the content the scan reads without another refusal: a byte at
least `0x20` and below `0x80`, no `0x22`, no `0x5C`.  On it the scan walks the body and returns `.ended`, so
the refusal names the opening quote at `pre.length` — the entry's own position.

## The UTF-8 premise, and why it is the route's

`RefusalOffset` splits on the stage that owns the refusal: a UTF-8-invalid document
refuses at its end, because the stage reports invalidity without a position
(`stage2.h:60-62`), and only a UTF-8-valid document's offset is the parser's.  The
walk runs after that stage, so its route is the valid-prefix branch; the geometry
does not carry the stage's verdict, so the premise is stated here rather than
derived.  On the other branch the clause is vacuous (`refusalOffset_quote`'s second
conjunct is discharged by the premise).

## Why the document hypothesis, and not the geometry alone

The staging's `entries` record the entry stream's positions, not its bytes: `inside`
bounds each position by the document's length and `order` orders them, and nothing
in `WalkGeom` ties `G.bs` at a position to a byte.  That the staged entries are the
emitter's lanes is the entry stage's composition (`JsonEntSpec` and the stage-1
emitter), outside this tree.  So the document's content is this route's parser-side
hypothesis, exactly as the flush route's whitespace-only document and the bracket's
and brace's are; the offset is not weakened by it, because the statement pins it at
the quote's own position — what `if.then205.i` stored.

The mark's two byte-agnostic facts are the bracket module's: `ne_ef_of_isSpaceB` and
`take3_ne_bom_of_getElem?_zero` are about the mark's `0xEF`, not about any
delimiter, so they are imported rather than restated.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffsetBrace

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The whitespace prefix before the quote

The parser's white-space skip is the definitional `spaceRun` over the carrier, whose
cons equation is `spaceRun_cons`.  A prefix of whitespace bytes contributes one to
the run per byte, and the quote byte ends it. -/

/-- **The run over a whitespace prefix, ended by the quote, is its length.**  Each
prefix byte is whitespace (`spaceRun_cons`'s true arm), and the quote is not
(`IsSpaceB 0x22 = false`), so the run stops there. -/
theorem spaceRun_literal_append_quote (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    spaceRun (ByteString.literal (pre ++ 0x22 :: rest)) = pre.length := by
  induction pre with
  | nil =>
      rw [List.nil_append, ByteString.literal_cons, spaceRun_cons]
      rfl
  | cons b pre ih =>
      rw [List.cons_append, ByteString.literal_cons, spaceRun_cons,
        ite_eq_left (hws b (by simp)), ih (fun x hx => hws x (by simp [hx]))]
      simp

/-- **The parser's skip stops at the quote.**  `skipFrom` from `0` is the run over
the document, which is the prefix's length. -/
theorem skipFrom_literal_append_quote (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    skipFrom (ByteString.literal (pre ++ 0x22 :: rest)) 0 = pre.length := by
  rw [skipFrom_def, ByteString.drop_zero,
    spaceRun_literal_append_quote pre rest hws, Nat.zero_add]

/-- **The byte at the prefix's end is the quote.**  The lookup skips the prefix and
reads the head of the remaining list. -/
theorem getElem?_append_quote (pre rest : List UInt8) :
    (pre ++ 0x22 :: rest)[pre.length]? = some 0x22 := by
  rw [List.getElem?_append, ite_eq_right (Nat.lt_irrefl _), Nat.sub_self]
  rfl

/-! ### The mark test's failure

`parseBytes` tests the three mark bytes before it parses, so its answer at this
document needs the test to fail.  A whitespace byte is not `0xEF`, and neither is
the quote; both facts are the bracket module's, stated over the byte rather than
the delimiter. -/

/-- **The mark test fails at a whitespace prefix and a quote.**  The first byte is a
whitespace byte (the prefix is non-empty) or the quote (it is empty), and neither is
the mark's `0xEF`. -/
theorem take3_ne_bom_append_quote (pre rest : List UInt8)
    (hws : ∀ b ∈ pre, IsSpaceB b = true) :
    (ByteString.literal (pre ++ 0x22 :: rest)).take 3
      ≠ ByteString.literal [0xEF, 0xBB, 0xBF] := by
  cases pre with
  | nil => exact take3_ne_bom_of_getElem?_zero (b := 0x22) (by simp) (by decide)
  | cons b pre =>
      exact take3_ne_bom_of_getElem?_zero (b := b) (by simp)
        (ne_ef_of_isSpaceB (hws b (by simp)))

/-! ### The string scan over an unterminated body

`parseKey` matches the opening quote and then scans the body from the byte after it.
A body of ASCII content is read byte by byte (`scanCharsFrom_ascii`) and
the scan reaches the end with `.ended` (`scanCharsFrom_nil`); the ASCII noncharacter
test is false (`isNoncharacter_false_of_lt_80`).  At `pre ++ 0x22 :: body` the scan's
cursor is the body's first byte, so the position scan's refusal is `.ended`. -/

/-- A body byte the unterminated-string scan reads as content: ASCII (at least
`0x20`, below `0x80`), excluding the closing quote and the escape introducer. -/
def IsQuoteBodyByte (b : UInt8) : Prop :=
  b ≠ 0x22 ∧ b ≠ 0x5C ∧ b < 0x80 ∧ 0x20 ≤ b.toNat

/-- **No ASCII byte is a Unicode noncharacter.**  The noncharacter set is
`U+FDD0..U+FDEF` plus the `U+nFFFE`/`U+nFFFF` code points, all at or above `0xFDD0`,
so a byte below `0x80` misses it. -/
theorem isNoncharacter_false_of_lt_80 {b : UInt8} (h : b < 0x80) :
    IsNoncharacter b.toNat = false := by
  have hlt : b.toNat < 0x80 := UInt8.lt_iff_toNat_lt.mp h
  have hmod : b.toNat % 0x10000 = b.toNat := Nat.mod_eq_of_lt (by omega)
  have h1 : ¬ 0xFDD0 ≤ b.toNat := by omega
  have h3 : ¬ b.toNat = 0xFFFE := by omega
  have h4 : ¬ b.toNat = 0xFFFF := by omega
  unfold IsNoncharacter
  rw [decide_eq_false h1, hmod, decide_eq_false h3, decide_eq_false h4]
  rfl

/-- **An ASCII-content body is scanned to its end.**  Each byte takes
`scanCharsFrom_ascii`'s accepting branch, the noncharacter test passes, and the
induction ends at the empty remainder's `.ended`. -/
theorem scanCharsFrom_body_ended (off : Nat) (body : List UInt8)
    (hbody : ∀ b ∈ body, IsQuoteBodyByte b) :
    scanCharsFrom off (ByteString.literal body) = .error .ended := by
  induction body generalizing off with
  | nil =>
      rw [show ByteString.literal ([] : List UInt8) = ByteString.empty from rfl]
      exact scanCharsFrom_nil off
  | cons b rest ih =>
      obtain ⟨hq, hs, hlt, hge⟩ := hbody b (by simp)
      rw [ByteString.literal_cons]
      rw [scanCharsFrom_ascii off b (ByteString.literal rest) hq hs hlt hge]
      unfold scanCons
      rw [ih (off + 1) (fun x hx => hbody x (by simp [hx]))]
      unfold okCons
      rw [isNoncharacter_false_of_lt_80 hlt]
      rfl

/-- **The scan from the opening quote's successor is `.ended`.**  The cursor after
`pre ++ 0x22` is the body's first byte, and the reference scan over the body ends at
the empty remainder. -/
theorem scanCharsEnd_quote_body (pre body : List UInt8)
    (hbody : ∀ b ∈ body, IsQuoteBodyByte b) :
    scanCharsEnd (ByteString.literal (pre ++ 0x22 :: body)) (pre.length + 1) 0 =
      .error .ended := by
  rw [scanCharsEnd_error]
  have hdropL : (pre ++ 0x22 :: body).drop (pre.length + 1) = body := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
    have hsub : pre.length + 1 - pre.length = 1 := by omega
    rw [hsub]
    rfl
  have hdropB : (ByteString.literal (pre ++ 0x22 :: body)).drop (pre.length + 1)
      = ByteString.literal body := by
    simp only [ByteString.drop, ByteString.data_toList_literal, hdropL]
  rw [hdropB]
  exact scanCharsFrom_body_ended 0 body hbody

/-! ### The key parser at an unterminated quote

`parseKey`'s opening-quote arm hands the body scan's reason to `rejectOf`.  When the
scan is `.ended`, that is `.unterminatedString` at the opening quote's index, which
is the position `parseKey` was called at. -/

/-- **The key parser reports `unterminatedString` at the opening quote.**  The byte
is the quote, and the body scan refuses `.ended`, which `rejectOf i` maps to the
opening quote's own index. -/
theorem parseKey_of_quote_ended {bs : Bytes} {i : Nat}
    (h : bs[i]? = some 0x22)
    (hs : scanCharsEnd bs (i + 1) 0 = .error .ended) :
    parseKey bs i = .fail (.invalid (.unterminatedString i)) := by
  unfold parseKey
  split
  · split
    · rename_i e he
      rw [hs] at he
      injection he with hh
      subst hh
      rfl
    · rename_i cs stop hok
      rw [hs] at hok
      cases hok
  · simp_all

/-- **The string parser reports `unterminatedString`.**  `parseString` forwards
`parseKey`'s refusal unchanged. -/
theorem parseString_of_quote_ended {bs : Bytes} {i : Nat}
    (h : bs[i]? = some 0x22)
    (hs : scanCharsEnd bs (i + 1) 0 = .error .ended) :
    parseString bs i = .fail (.invalid (.unterminatedString i)) := by
  simp only [parseString, parseKey_of_quote_ended h hs]

/-- **The value parser reports `unterminatedString` at the quote.**  `0x22` is the
string opener's arm, so the value parser enters `parseString` at its own index. -/
theorem parseValue_of_quote_ended {bs : Bytes} {i depth : Nat}
    (h : bs[i]? = some 0x22)
    (hs : scanCharsEnd bs (i + 1) 0 = .error .ended) :
    parseValue bs i depth = .fail (.invalid (.unterminatedString i)) := by
  rw [parseValue.eq_def]
  split
  all_goals first
    | exact parseString_of_quote_ended h hs
    | simp_all

/-! ### The parser's refusal at the document -/

/-- **The parser refuses a whitespace-prefixed unterminated quote at the quote.**
The input bound is met and the mark test fails, so `parseBytes` enters `parseValue` at
the skipped-to cursor — the quote — where the string arm's body scan is `.ended` and
the refusal names the opening quote. -/
theorem parseBytes_spacePrefix_quote {pre body : List UInt8}
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbody : ∀ b ∈ body, IsQuoteBodyByte b)
    (hbound : (pre ++ 0x22 :: body).length ≤ Limits.default.maxInput) :
    parseBytes Limits.default (ByteString.literal (pre ++ 0x22 :: body)) =
      .error (.invalid (.unterminatedString pre.length)) := by
  have hskip := skipFrom_literal_append_quote pre body hws
  have hscan := scanCharsEnd_quote_body pre body hbody
  have hfail := parseValue_of_quote_ended
    (bs := ByteString.literal (pre ++ 0x22 :: body))
    (i := skipFrom (ByteString.literal (pre ++ 0x22 :: body)) 0)
    (depth := Limits.default.maxDepth)
    (by rw [hskip, ByteString.getElem?_literal]; exact getElem?_append_quote pre body)
    (by rw [hskip]; exact hscan)
  unfold parseBytes
  rw [ite_eq_right (by rw [literal_length]; omega),
    ite_eq_right (take3_ne_bom_append_quote pre body hws)]
  split
  · rename_i p hp
    rw [hfail] at hp
    cases hp
  · rename_i e hp
    have he : e = .invalid
        (.unterminatedString
          (skipFrom (ByteString.literal (pre ++ 0x22 :: body)) 0)) := by
      rw [hp] at hfail
      injection hfail with h
    rw [he, hskip]

/-! ### The refusal offset -/

/-- **The quote route's refusal offset is the parser's.**  At a document whose
prefix is whitespace, whose next byte is `0x22`, and whose body never closes the
string, on the walk's UTF-8-valid branch, every refusal the parser reports is
`.unterminatedString` at the opening quote — or the byte-order mark, which carries
no position and which this document cannot open with — so `RefusalOffset` holds at
the quote's position. -/
theorem refusalOffset_quote {pre body : List UInt8}
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbody : ∀ b ∈ body, IsQuoteBodyByte b)
    (hbound : (pre ++ 0x22 :: body).length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window (pre ++ 0x22 :: body)
      (pre ++ 0x22 :: body).length (pipelineBlocks (pre ++ 0x22 :: body).length))) :
    RefusalOffset (pre ++ 0x22 :: body) pre.length := by
  have hparse := parseBytes_spacePrefix_quote hws hbody hbound
  unfold RefusalOffset
  dsimp only
  refine ⟨?_, fun hnot => absurd hutf8 hnot⟩
  intro _ r hr
  rw [hparse] at hr
  have hr' : r = .unterminatedString pre.length := by
    injection hr with h1
    injection h1 with h2
    exact h2.symm
  subst hr'
  simp [rejectPos]

/-- **The quote route's offset, at the geometry's document.**  The arm's store writes
`%idxprom.i`'s word, which `WalkInv.idx_reg` carries as `entryPos G C.k`; the document's
prefix is the whitespace the parser skips and its next byte is the opening quote, so
the parser's refusal is that position.  The document's content and the stage's
validity are stated here, for the reasons the module gives. -/
theorem walkRefusalOffset_quote {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {pre body : List UInt8} (hbs : G.bs = pre ++ 0x22 :: body)
    (hpos : pre.length = entryPos G C.k)
    (hws : ∀ b ∈ pre, IsSpaceB b = true)
    (hbody : ∀ b ∈ body, IsQuoteBodyByte b)
    (hbound : G.bs.length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window G.bs G.bs.length (pipelineBlocks G.bs.length))) :
    RefusalOffset G.bs (entryPos G C.k) := by
  rw [← hpos]
  rw [hbs] at hbound hutf8 ⊢
  exact refusalOffset_quote hws hbody hbound hutf8

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.spaceRun_literal_append_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spaceRun_literal_append_quote

/-- info: 'LeanLLVM.Refinement.skipFrom_literal_append_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms skipFrom_literal_append_quote

/-- info: 'LeanLLVM.Refinement.getElem?_append_quote' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getElem?_append_quote

/-- info: 'LeanLLVM.Refinement.take3_ne_bom_append_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take3_ne_bom_append_quote

/-- info: 'LeanLLVM.Refinement.isNoncharacter_false_of_lt_80' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isNoncharacter_false_of_lt_80

/-- info: 'LeanLLVM.Refinement.scanCharsFrom_body_ended' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scanCharsFrom_body_ended

/-- info: 'LeanLLVM.Refinement.scanCharsEnd_quote_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scanCharsEnd_quote_body

/-- info: 'LeanLLVM.Refinement.parseKey_of_quote_ended' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseKey_of_quote_ended

/-- info: 'LeanLLVM.Refinement.parseString_of_quote_ended' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseString_of_quote_ended

/-- info: 'LeanLLVM.Refinement.parseValue_of_quote_ended' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseValue_of_quote_ended

/-- info: 'LeanLLVM.Refinement.parseBytes_spacePrefix_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseBytes_spacePrefix_quote

/-- info: 'LeanLLVM.Refinement.refusalOffset_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_quote

/-- info: 'LeanLLVM.Refinement.walkRefusalOffset_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkRefusalOffset_quote

end LeanLLVM.Refinement
