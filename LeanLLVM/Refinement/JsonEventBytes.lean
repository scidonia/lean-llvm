/-
The consumer's event stream read back into its events.

`consumeBytes` (`JsonStage2NoEvent`) reads a stream the certified walk wrote and
produces the events a consumer sees.  `valueOf` in the route needs the same
reading as a value, but it is holding the pipeline's returned buffers rather than
a trace: the event bytes and the arena prefix, with the document beside them.
This module is that reader — `eventsOfBytes` walks the emitted encoding record by
record and returns the events, or `none` where the stream cannot be read as one.

# The encoding it inverts

`kernel/json/stage2.h` fixes the record widths: a container or literal tag is one
byte; a number (`T_NUM`, 7) is its tag and eight little-endian IEEE bytes; a key
(`T_KEY`, 5) or string (`T_STR`, 6) is its tag, the decoded length as four
little-endian bytes, and eight bytes whose top bit selects the body's source.  A
set top bit is a span into the document — the plain form, whose body is the input
bytes at the low bits and which the arena does not hold — and a clear top bit is
an offset into the arena prefix — the escaped form, whose decoded bytes the walk
appended there.  The record reader is `consumeBytes`'s, and the field's two forms
are `stringConsumer`'s: the same bit test, the same `take len` slice, and the
same `escapeCodePoints` decoding.  The document is therefore a parameter: a
plain body cannot be read from the event stream and the arena alone.

# `none` is "not readable here", not a refusal

A record that runs past the stream, a field whose slice runs past its source, or
a body that does not decode yields `none`.  That says nothing about the
document's validity: the caller falls back to the reference parser, which is the
only authority on acceptance and on a refusal's reason and offset.  A stream the
walk wrote for an accepted document reads as its events; a refusing run's stream
is a prefix and is not asked for.

`valueOfEvents` (`JsonEventDecode`) is the value side of this reader.
-/
import LeanLLVM.Refinement.JsonEventDecode
import LeanLLVM.Refinement.JsonEscapeSpec

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- A string or key record's decoded body.  The record's field names its source
— the arena prefix for the clear-bit escaped form, the document for the
top-bit-set plain form — and the body is that source's `len`-byte slice.  The
plain form recomputes the token's span (the field clears to the body's first
byte, `len` is the raw body's byte count) and reads it with the escape-aware
scan; the arena form reads its own UTF-8 slice.  `none` when the slice runs past
its source or its bytes do not decode. -/
def recordBodyCodePoints (bs arena : List UInt8) (len field : Nat) :
    Option (List Nat) :=
  if field < 2 ^ 63 then
    if field + len ≤ arena.length then
      escapeCodePoints ((arena.drop field).take len)
    else none
  else
    let off := field - 2 ^ 63
    if off + len ≤ bs.length then
      bodyCodePointsAt bs off
    else none

/-- The walk: one record at a time, at the widths `kernel/json/stage2.h`
documents.  Every recursive call is on a shorter suffix, which the truncation
checks above it establish. -/
def walkRecords (bs arena : List UInt8) : List UInt8 →
    Option (List ConsumerEvent)
  | [] => some []
  | b :: rest =>
      match b.toNat with
      | 1 => (ConsumerEvent.kind 1 :: ·) <$> walkRecords bs arena rest
      | 2 => (ConsumerEvent.kind 2 :: ·) <$> walkRecords bs arena rest
      | 3 => (ConsumerEvent.kind 3 :: ·) <$> walkRecords bs arena rest
      | 4 => (ConsumerEvent.kind 4 :: ·) <$> walkRecords bs arena rest
      | 8 => (ConsumerEvent.kind 8 :: ·) <$> walkRecords bs arena rest
      | 9 => (ConsumerEvent.kind 9 :: ·) <$> walkRecords bs arena rest
      | 10 => (ConsumerEvent.kind 10 :: ·) <$> walkRecords bs arena rest
      | 5 =>
          if rest.length < 12 then none
          else
            let len := bytesToNat (rest.take 4)
            let field := bytesToNat ((rest.drop 4).take 8)
            match recordBodyCodePoints bs arena len field with
            | some cps =>
                (ConsumerEvent.str true len field cps :: ·) <$>
                  walkRecords bs arena (rest.drop 12)
            | none => none
      | 6 =>
          if rest.length < 12 then none
          else
            let len := bytesToNat (rest.take 4)
            let field := bytesToNat ((rest.drop 4).take 8)
            match recordBodyCodePoints bs arena len field with
            | some cps =>
                (ConsumerEvent.str false len field cps :: ·) <$>
                  walkRecords bs arena (rest.drop 12)
            | none => none
      | 7 =>
          if rest.length < 8 then none
          else
            (.number (bytesToNat (rest.take 8)) :: ·) <$>
              walkRecords bs arena (rest.drop 8)
      | _ => none
termination_by evs => evs.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_drop]
    omega

/-- **The consumer's events read back from the emitted stream.**  `bs` is the
document, `evs` the event bytes and `arena` the arena prefix; the result is the
events `consumeBytes` would read from the same three, or `none` where a record is
truncated or a string body cannot be read from the source its field names. -/
def eventsOfBytes (bs evs arena : List UInt8) : Option (List ConsumerEvent) :=
  walkRecords bs arena evs

end LeanLLVM.Refinement
