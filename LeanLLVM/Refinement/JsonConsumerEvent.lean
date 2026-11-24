/-
The consumer's event record and the stream's tag constants.

`ConsumerEvent` is one event as the caller's fold sees it, and the tags it carries
are the emitted encoding's (`stage2.c`'s `T_KEY`/`T_STR`, `JsonStage2Body`'s
`T_NUM`).  Both are here rather than in the modules that prove the walk, so a
program that decodes an event stream depends on the vocabulary alone and not on
the walk's specification: `JsonStage2Body` proves the emitted numbers against the
strtod tiers, and importing it would put that theory — and the ITree and Mathlib
imports the tiers use — behind the record's definition.
-/
set_option autoImplicit false

namespace LeanLLVM.Refinement

/-- `T_NUM` (`stage2.c:104`). -/
def stage2TagNum : Nat := 7

namespace EventRecord

/-- `T_KEY` (`stage2.c:104`, pinned in `JsonStage2Body`). -/
def tagKey : Nat := 5

/-- `T_STR`. -/
def tagStr : Nat := 6

end EventRecord

/-- One event as the caller's fold sees it: the tag byte, the two payload fields
the record carries, and — for a string — the code points the body decodes to.  The
`len`/`payload` fields are the record's own so the fold can add exactly what the
emitted bytes would have carried; `cps` is the decoded body, which is what a
consumer that wants the string reads off the document or the arena. -/
structure ConsumerEvent where
  /-- The record's first byte: `T_OBJ`, `T_OBJ_END`, `T_ARR`, `T_ARR_END`,
  `T_KEY`, `T_STR`, `T_NUM`, `T_TRUE`, `T_FALSE` or `T_NULL`. -/
  tag : Nat
  /-- The four-byte length a key or string record carries; zero otherwise. -/
  len : Nat
  /-- A number's eight payload bits, or a key's/string's eight-byte field. -/
  payload : Nat
  /-- The decoded body's code points; empty for a non-string event. -/
  cps : List Nat
deriving DecidableEq, Repr

namespace ConsumerEvent

/-- A container marker or literal tag. -/
def kind (t : Nat) : ConsumerEvent :=
  ⟨t, 0, 0, []⟩

/-- A number: `T_NUM` and the payload the record would hold. -/
def number (bits : Nat) : ConsumerEvent :=
  ⟨stage2TagNum, 0, bits, []⟩

/-- A key or string: `T_KEY`/`T_STR`, the length, the span-or-arena field, and
the decoded code points. -/
def str (key : Bool) (len field : Nat) (cps : List Nat) : ConsumerEvent :=
  ⟨(if key then EventRecord.tagKey else EventRecord.tagStr), len, field, cps⟩

/-- The consumer's per-record contribution to its sum: `tag + len + payload`. -/
def terms (e : ConsumerEvent) : Nat :=
  e.tag + e.len + e.payload

end ConsumerEvent

end LeanLLVM.Refinement
