/-
The staging's document-window separations, and what the escape call's frame
leaves of the document.

`s1BlocksPre` stages the padded window at `b` and the three UTF-8 zero bytes at
`b - 3`.  The run's writable objects are the entry array at `ent`, the escape
stream at `xp`, the count slot at `nxp` and the carry slot at `xcarry`; the pre
orders every one of them against the window *and* the three bytes before it, so
a store at any of them is outside both.  The entry array's separation is the
loop's own (`b + 64 * blocksOf n ≤ ent`, the gap its stores rely on); the escape
call's three regions are the ones this module reads.

The loop's induction carries two caller facts about the escape call: the
selection answers it (`hcall`) and its answer keeps the document and the staged
zeroes (`hkeep`).  `hcall` is the escape unit's own record at the call's
arguments.  `hkeep` is a consequence of the pre and the call's frame: the escape
record's `EscapeReach` permits a change only inside the stream's touched extent,
the count's eight bytes and the carry's sixteen, and the pre orders those three
regions against the window.  `s1BlocksPre_escape_keeps_document` states that
consequence at the pre's own numbers, in the per-block and prefix form the loop
consumes.

The frame's stream extent is the *touched* one,
`4 * (xn0 + position.length + batchReserve)`, while the pre stages the capacity
`4 * (xn + 64 * blocksOf n + batchReserve)`.  The theorem takes the call's room
`xn0 + position.length ≤ xn + 64 * blocksOf n` as a premise: the loop's count
advances by the positions it emits, so this is its own accounting over the
document.  A caller that holds the frame at the block's extent gets the
capacity's silence from that bound; nothing here assumes the call's count is
the staging's initial count.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonEscapeCallFrame

namespace LeanLLVM.Refinement.JsonS1BlocksSeparation

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-! ### The pre's layout, at its own witnesses -/

/-- **The staging's layout.**  The pre read at its own numbers: the padded
window, the three staged zeroes, the count slot's word, and the separations that
keep the window and the prefix from the entry array and the escape call's three
regions.  The escape stream's separation is at the whole staged capacity, as
`xp`'s presence clause is. -/
theorem s1BlocksPre_layout {args : List Value} {mem : Mem} {next : Nat}
    (h : s1BlocksPre args mem next) :
    ∃ (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] ∧
      3 ≤ b ∧
      readBytes mem (b - 3) 3 = some [0, 0, 0] ∧
      readBytes mem b (64 * blocksOf bs.length) = some (padded bs) ∧
      readBytes mem nxp 8 = some (wordBytes 8 xn) ∧
      (b + 64 * blocksOf bs.length ≤ xp ∨
        xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ b - 3) ∧
      (b + 64 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ b - 3) ∧
      (b + 64 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ b - 3) := by
  unfold s1BlocksPre at h
  obtain ⟨b, ent, xp, nxp, xcarry, arm, bs, xn, hargs, hb3, hzero, _hbs63,
    hdoc, _hent, hxn, _hxn63, _hxpHas, _hxcRead, _hblkcap, _hentPrefix,
    hxp, hnxp, hxc, _hentXp, _hentNxp, _hentXc, _hxpNxp, _hxpXc, _hnxpXc⟩ := h
  exact ⟨b, ent, xp, nxp, xcarry, xn, arm, bs, hargs, hb3, hzero, hdoc, hxn,
    hxp, hnxp, hxc⟩

/-! ### The staged document region

The pipeline's staging lists the document's window and its three prefix bytes as
one region, `(b - 3, 3 + 64 * B)`, with the decoder's 32-byte read-past tail as
a second entry.  Whichever writable region `DisjointRegions` orders against the
first of those is ordered against exactly the window and the prefix the block
unit's pre states, so the pre's three clauses are the staging's own pairwise
promise at that entry.  The lemma records the step; the pipeline's `nxp0` is the
pre's count value, so the stream's widths are the same number. -/

/-- **A separated staged document region gives the pre's three clauses.**
`(b - 3, 3 + 64 * B)` is the pipeline's document entry — the window together
with the three bytes before it — so a writable region's separation from that
entry at the count's capacity is the pre's clause at the same numbers. -/
theorem clauses_of_document_region {b xp nxp xcarry cap B : Nat} (hb3 : 3 ≤ b)
    (hxp : (b - 3) + (3 + 64 * B) ≤ xp ∨ xp + cap ≤ b - 3)
    (hnxp : (b - 3) + (3 + 64 * B) ≤ nxp ∨ nxp + 8 ≤ b - 3)
    (hxc : (b - 3) + (3 + 64 * B) ≤ xcarry ∨ xcarry + 16 ≤ b - 3) :
    (b + 64 * B ≤ xp ∨ xp + cap ≤ b - 3) ∧
      (b + 64 * B ≤ nxp ∨ nxp + 8 ≤ b - 3) ∧
      (b + 64 * B ≤ xcarry ∨ xcarry + 16 ≤ b - 3) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hxp with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  · rcases hnxp with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  · rcases hxc with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h

/-! ### The frame's silence over the window and the prefix -/

/-- **The escape call's three regions leave the window alone.**  The frame names
the stream's extent `cap`, the count's eight bytes and the carry's sixteen; the
separations put each of them entirely before the prefix (`b - 3`) or entirely
after the window's end.  A block read lies wholly on one side of every region,
so it is the caller's. -/
theorem readBytes_window_of_escape_frame {mem0 M : Mem}
    {b xp xn xcarry cap B j : Nat}
    (hframe : UnchangedOutside mem0 M [(xp, cap), (xn, 8), (xcarry, 16)])
    (hxp : b + 64 * B ≤ xp ∨ xp + cap ≤ b - 3)
    (hnxp : b + 64 * B ≤ xn ∨ xn + 8 ≤ b - 3)
    (hxc : b + 64 * B ≤ xcarry ∨ xcarry + 16 ≤ b - 3)
    (hj : j < B) :
    readBytes M (b + 64 * j) 64 = readBytes mem0 (b + 64 * j) 64 := by
  refine readBytes_of_outside_three hframe ?_ ?_ ?_
  · intro k _
    have hsep : b + 64 * j + 64 ≤ xp ∨ xp + cap ≤ b + 64 * j := by
      rcases hxp with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact outside_of_separated hsep (by omega) (by omega)
  · intro k _
    have hsep : b + 64 * j + 64 ≤ xn ∨ xn + 8 ≤ b + 64 * j := by
      rcases hnxp with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact outside_of_separated hsep (by omega) (by omega)
  · intro k _
    have hsep : b + 64 * j + 64 ≤ xcarry ∨ xcarry + 16 ≤ b + 64 * j := by
      rcases hxc with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact outside_of_separated hsep (by omega) (by omega)

/-- **The escape call's three regions leave the three staged zeroes alone.**  The
prefix `[b - 3, b)` is contiguous with the window, and each separation puts its
region entirely before the prefix or at the window's end, so the three bytes read
as the caller staged them. -/
theorem readBytes_prefix_of_escape_frame {mem0 M : Mem}
    {b xp xn xcarry cap B : Nat} (hb3 : 3 ≤ b)
    (hframe : UnchangedOutside mem0 M [(xp, cap), (xn, 8), (xcarry, 16)])
    (hxp : b + 64 * B ≤ xp ∨ xp + cap ≤ b - 3)
    (hnxp : b + 64 * B ≤ xn ∨ xn + 8 ≤ b - 3)
    (hxc : b + 64 * B ≤ xcarry ∨ xcarry + 16 ≤ b - 3) :
    readBytes M (b - 3) 3 = readBytes mem0 (b - 3) 3 := by
  refine readBytes_of_outside_three hframe ?_ ?_ ?_
  · intro k _
    have hsep : (b - 3) + 3 ≤ xp ∨ xp + cap ≤ b - 3 := by
      rcases hxp with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    exact outside_of_separated hsep (by omega) (by omega)
  · intro k _
    have hsep : (b - 3) + 3 ≤ xn ∨ xn + 8 ≤ b - 3 := by
      rcases hnxp with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    exact outside_of_separated hsep (by omega) (by omega)
  · intro k _
    have hsep : (b - 3) + 3 ≤ xcarry ∨ xcarry + 16 ≤ b - 3 := by
      rcases hxc with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    exact outside_of_separated hsep (by omega) (by omega)

/-! ### The loop's `hkeep`, from the pre -/

/-- **The escape call keeps the document and the staged zeroes.**  At the pre's
numbers, a returned memory that differs from the caller's only inside the escape
call's three regions reads each document block and the three bytes before it as
the caller staged them.  The stream's frame extent is the touched one,
`4 * (xn0 + len + batchReserve)`, at the call's own count `xn0` and position
count `len`; `xn0 + len ≤ xn + 64 * blocksOf n` orders it against the staged
capacity `4 * (xn + 64 * blocksOf n + batchReserve)` in the pre's separation.
The count's room over the whole document is the loop's own accounting, so it
stays a premise rather than a consequence of the staging.

The conclusion is exactly the loop's `hkeep`: the per-block reads at `docBlock`
and the prefix's three zeroes.  The blocks are the pre's own window read, split
per block by `readBytes_docBlock`. -/
theorem s1BlocksPre_escape_keeps_document {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s1BlocksPre args mem next) :
    ∃ (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] ∧
      3 ≤ b ∧
      (b + 64 * blocksOf bs.length ≤ xp ∨
        xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ b - 3) ∧
      (b + 64 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ b - 3) ∧
      (b + 64 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ b - 3) ∧
      ∀ (M : Mem) (xn0 len : Nat),
        xn0 + len ≤ xn + 64 * blocksOf bs.length →
        UnchangedOutside mem M (escapeCallRegions xp nxp xcarry (xn0 + len)) →
        (∀ j, j < blocksOf bs.length →
          readBytes M (b + 64 * j) 64 = some (docBlock bs j)) ∧
        readBytes M (b - 3) 3 = some [0, 0, 0] := by
  obtain ⟨b, ent, xp, nxp, xcarry, xn, arm, bs, hargs, hb3, hzero, hdoc, _hxn,
    hxp, hnxp, hxc⟩ := s1BlocksPre_layout hpre
  refine ⟨b, ent, xp, nxp, xcarry, xn, arm, bs, hargs, hb3, hxp, hnxp, hxc, ?_⟩
  intro M xn0 len hroom hframe
  have hcap : 4 * (xn0 + len + batchReserve) ≤
      4 * (xn + 64 * blocksOf bs.length + batchReserve) := by omega
  have hxpT : b + 64 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn0 + len + batchReserve) ≤ b - 3 := by
    rcases hxp with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  refine ⟨fun j hj => ?_, ?_⟩
  · -- the block the caller staged reads through the call's frame
    rw [readBytes_window_of_escape_frame hframe hxpT hnxp hxc hj]
    exact readBytes_docBlock mem bs b hdoc hj
  · rw [readBytes_prefix_of_escape_frame hb3 hframe hxpT hnxp hxc]
    exact hzero

/-! ### Axiom footprints

The separations are inequalities from the pre; the frame is the escape record's
`UnchangedOutside` and `readBytes_of_outside_three`; the document split is
`readBytes_docBlock`.  Nothing here states a new memory fact. -/

#print axioms s1BlocksPre_layout
#print axioms clauses_of_document_region
#print axioms readBytes_window_of_escape_frame
#print axioms readBytes_prefix_of_escape_frame
#print axioms s1BlocksPre_escape_keeps_document

end LeanLLVM.Refinement.JsonS1BlocksSeparation
