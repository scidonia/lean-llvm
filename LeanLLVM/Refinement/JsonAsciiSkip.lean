/-
The ASCII shortcut's specification-level soundness.

The block unit's first body returned `1` exactly when every document byte is
below `0x80` (`s1_blocks.h` at v1); its v2 body returns that answer in bit 0 and
the UTF-8 stage's error word in bit 1, with the DFA fused into the block loop.
The ASCII shortcut now runs inside that loop: an all-ASCII block whose
predecessor is ASCII skips the DFA, and a document whose every byte is ASCII
needs no DFA work at all.  The two facts that make the skip sound — and the
v1 consumer's reading "the window is a valid UTF-8 prefix, so the UTF-8 unit can
be skipped" — are stated here at the specification's own predicates, not by
running the unit:

* `utf8WinPrefix_of_ascii` — a window whose every byte is ASCII is a valid UTF-8
  prefix, because each byte is a one-byte `Utf8Char.one` and `ValidPrefix` admits
  a string of complete characters (`validPrefix_of_utf8Chars`).  The window's
  three zero prefix bytes and its zero padding are ASCII too, so the fact needs
  no hypothesis about the block count;
* `skip_sound` — the composed statement for a document whose bytes are ASCII:
  the window the pipeline stages is a valid prefix, which is exactly the
  predicate `Γ_utf8.post`'s refusal clause is stated over
  (`err' = 0 ↔ utf8WinPrefix (utf8Window …)`).

The unit's own return is related to `(∀ x ∈ bs, x.toNat < 0x80)` by
`ascii_padded_iff` (`JsonEntSpec.lean`); this module only closes the step from
that predicate to the validity relation.  What is *not* claimed: an all-ASCII
document is UTF-8 valid, not parse-accepted — stage 2 still decides the parse and
owns the refusal offset.
-/
import LeanLLVM.Refinement.JsonEntSpec
import LeanLLVM.Refinement.JsonUtf8IR

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonScanSpec

/-- An all-ASCII byte list is a string of complete UTF-8 characters. -/
theorem utf8Chars_literal_of_ascii (l : List UInt8)
    (h : ∀ x ∈ l, x.toNat < 0x80) : Utf8Chars (ByteString.literal l) := by
  induction l with
  | nil =>
      exact Utf8Spans.nil _
  | cons b bs ih =>
      rw [ByteString.literal_cons]
      refine Utf8Spans.char (Utf8Char.one (b := b) (rest := ByteString.literal bs) ?_)
        (ih (fun x hx => h x (by simp [hx])))
      exact h b (by simp)

/-- **An all-ASCII window is a valid UTF-8 prefix.** -/
theorem utf8WinPrefix_of_ascii {win : List UInt8}
    (h : ∀ x ∈ win, x.toNat < 0x80) : utf8WinPrefix win := by
  unfold utf8WinPrefix
  exact validPrefix_of_utf8Chars (utf8Chars_literal_of_ascii win h)

/-- **The skip is sound.**  For an ASCII document, the window the pipeline stages
— three zero prefix bytes, the document and zero padding to the block count — is
a valid UTF-8 prefix.  The prefix and padding bytes are zero, which the ASCII
predicate admits, so the statement carries no block-count side condition. -/
theorem skip_sound (bs : List UInt8) (h : ∀ x ∈ bs, x.toNat < 0x80) :
    utf8WinPrefix (utf8Window bs bs.length (blocksOf bs.length)) := by
  apply utf8WinPrefix_of_ascii
  intro x hx
  unfold utf8Window at hx
  rcases List.mem_append.mp hx with hpre | hrest
  · rcases List.mem_append.mp hpre with hpre | hdoc
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hpre
      decide
    · exact h x hdoc
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hrest
    decide

end LeanLLVM.Refinement
