/-
The last entry's run class, at a staged document.

## What is exhibited

`LastEntryArm.run` is the default arm's run class at the last entry: the byte before the
entry's end is whitespace, so the whitespace skip runs, the token's end `%ee.1.i` is the
run's stop, the copy call's test is true and the extra-token scan is entered; the merge
that follows is the terminal one, `WalkDispatchResult.mergeLast`, because its index is the
stream's end.

The document below is the terminal level's, a letter followed by the whitespace the run
stops at:

| document | head byte | `HeadArm` | bytes | entries |
|---|---|---|---|---|
| `"a "` | `97` (`'a'`) | `defaultValueBracketHigh` | `[97, 32]` | one, at `0` |

The document's length is two, so the last entry's end `%4` is `2` and the byte before it is
the space at index `1` — exactly the class's premise, read off the document rather than
assumed.  The state is the seed's own handoff (`walkSeedInvariant_geometry`), so the head
byte is the document's and the dispatch below runs through the real `LastEntryArm.dispatch`.

The bundle's other fields are the arm's own premises, as they are for the continuing run
class: the whitespace run's bytes, the three callees' staging, the landing's byte and the
visits' totality are the input's, and no `WalkInv` clause fixes them.  What the dispatch
below exercises is what the arm composes: `runLastMerge_at`'s path, the merge's cells and
`mergeLast`'s price.

## The terminal index, and the two readings of the credit

`entryPos G 1 = 0` at this document (`entryPos_one`): past the last entry the *stream*
position totalises to zero, so a terminal price read through `entryPos` charges nothing for
the document the walk has left.  That is why `mergeLast` states its byte term at the credit
boundary — `boundary G 1 = G.n = 2` — and why the bundle carries the run's count and start
as document bounds rather than as a budget: `runLastMerge_at` turns them into the price with
`runLast_price_with_credit`.  `spaceVisits_le` is the same document's arrow on the scan: the
scan's bound is the document's length, two (`hspanDoc`), so the visits `4·(2 - 1 - i)` are
at most four — the trailing whitespace of a two-byte document cannot be longer.

## The controls

`spaceNotSpanStart` is about the price's *shape*: the continuing bundle's
`RunFacts.hspanStart` places the scan inside `entryPos G (C.k + 1)`, which at the terminal
index is `entryPos G 1 = 0`.  A scan whose bound is the document's length two is not inside
it, so the continuing bundle cannot describe this run at the last entry — the split into
`RunFacts` and `RunLastFacts` is not bookkeeping.  The byte-level pair is `spaceByte_stop`
and `spaceByte_start_cont`: the space at index one *stops* the skip, and the letter at index
zero is a byte the skip advances over rather than its stop (`spaceByte_stop_not_entry`), so
the run is the document's second byte and not the entry's first.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchArmsDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

namespace WalkScope

/-! ### The staged document -/

/-- **A document of one entry whose last byte is a space.**  The bytes are `c` and `32`,
the entry stream holds a single lane zero, and the document's length is two, so the last
entry's end is the document's end and the byte before it is the space. -/
structure TrailingSpaceDocument {m0 : Mem} (G : WalkGeom m0) (c : UInt8) : Prop where
  /-- The document is two bytes long. -/
  len : G.n = 2
  /-- The entry stream holds one entry: this is the last one. -/
  count : G.nep = 1
  /-- The document is the byte `c` followed by a space. -/
  bytes : readBytes m0 G.b 2 = some [c, 32]
  /-- The entry stream's lane is zero. -/
  lane : readLanes32 m0 G.ep 1 = some [0]

/-- The document's byte list is the read's, at `len`. -/
theorem TrailingSpaceDocument.bs {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TrailingSpaceDocument G c) : G.bs = [c, 32] := by
  have hread : readBytes m0 G.b G.n = some [c, 32] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The document's entry stream is the read's, at `count`. -/
theorem TrailingSpaceDocument.ent {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TrailingSpaceDocument G c) : G.ent = [0] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0] := by rw [h.count]; exact h.lane
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The document's entry is at position zero. -/
theorem TrailingSpaceDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TrailingSpaceDocument G c) : entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- **The position past the only entry is zero.**  `entryPos` is the lane list's `getD`,
so past its length it totalises to zero — the terminal index's empty byte span, at this
document. -/
theorem TrailingSpaceDocument.entryPos_one {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TrailingSpaceDocument G c) : entryPos G 1 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The document's byte at the entry is `c`. -/
theorem TrailingSpaceDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TrailingSpaceDocument G c) : entryByte G 0 = c := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [c, 32] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-! ### The head byte, at the staged document -/

/-- **`"a "`'s head byte is `97`.**  The seeded head's `%8` is the document's byte at the
carried index, and the carried index is the first entry's. -/
theorem runLastHead_a {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TrailingSpaceDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)) := by
  have h0 : entryByte G (walkSeed G S).k = 97 := by
    have hk : (walkSeed G S).k = 0 := rfl
    rw [hk]
    exact h.entryByte_zero
  have hiter := hInv.iter.reg8
  rw [h0] at hiter
  have ht : ((97 : UInt8)).toNat = 97 := by decide
  rw [ht] at hiter
  walk_read using hiter

/-- **`97`'s head class is the default arm's**: `91 ≤ 97 < 123`, `93 ≤ 97` and `97 ≠ 93` —
the `NodeBlock19 → NodeBlock11 → LeafBlock9 → sw.default.i` route. -/
theorem runLastClass_a : HeadArm (BitVec.ofNat 8 97) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`97` takes the run class's premise**: the tag test is clear there, so the seam sends
the walk to `if.else387.i` and the byte's span rather than the plain-value path. -/
theorem runLastPrem_a :
    (evalICmp .eq (BitVec.ofNat 8 97) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 97 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-! ### The arm at the document, and its dispatch -/

/-- **The document fixes the bundle's head byte.**  The bundle's `%8` cell and the
document's are the same read, so its `x` is `97` rather than an unrelated byte. -/
theorem runLastFacts_byte {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TrailingSpaceDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    (f : RunLastFacts G (walkSeed G S) s) : f.x = BitVec.ofNat 8 97 := by
  have h8d := runLastHead_a G S s h hInv
  have hinj := Option.some.inj (f.h8.symm.trans h8d)
  exact eq_of_heq (Value.int.inj hinj).2

/-- **`"a "`'s head takes the last entry's run arm.**  The bundle is the arm's own
premises, and `runLastFacts_byte` says its head byte is the document's. -/
def run_last_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (f : RunLastFacts G (walkSeed G S) s) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .run f

/-- **The dispatch at `"a "`**, through the real `LastEntryArm.dispatch`: the entry stream
is exhausted (`¬ (0 + 1 < 1)`), the run's segment is `runLastMerge_at`'s, and the result is
`mergeLast` at the stream's end with the entry allowance's price. -/
theorem run_last_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TrailingSpaceDocument G (97 : UInt8))
    (f : RunLastFacts G (walkSeed G S) (openerHead G S args next)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hnot : ¬ ((walkSeed G S).k + 1 < G.nep) := by
    rw [h.count]
    show ¬ (0 + 1 < 1)
    omega
  exact LastEntryArm.dispatch (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hnot
    (run_last_arm G S _ f)

/-! ### The terminal index's arithmetic, at the document -/

/-- **The scan's visits are at most four, at a two-byte document.**  The bundle's bound is
inside the document (two bytes, `hspanDoc`), so `c - 1 - i ≤ 1` and `4·(c - 1 - i) ≤ 4`:
the trailing whitespace a two-byte document can hold is one byte, and the price it can
charge for the scan is its four links. -/
theorem spaceVisits_le {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (h : TrailingSpaceDocument G (97 : UInt8)) (f : RunLastFacts G C s) :
    4 * (f.c - 1 - f.i) ≤ 4 := by
  have hc : f.c ≤ 2 := by
    rw [← h.len]
    exact f.hspanDoc
  have hi := f.hic
  omega

/-! ### The controls -/

/-- **The continuing bundle's span field cannot hold at the terminal index.**  A scan whose
bound is the document's length (`2`) is not inside `entryPos G 1`, which is `0` — this is
the fact that makes `RunLastFacts` a separate bundle rather than `RunFacts` reused. -/
theorem spaceNotSpanStart {m0 : Mem} (G : WalkGeom m0) (h : TrailingSpaceDocument G
    (97 : UInt8)) : ¬ ((2 : Nat) ≤ entryPos G 1) := by
  rw [h.entryPos_one]
  omega

/-- **The document's second byte stops the skip.**  `wsStop G 1` holds at the space: the
run's stop is the byte before the entry's end. -/
theorem spaceByte_stop {m0 : Mem} (G : WalkGeom m0) (h : TrailingSpaceDocument G
    (97 : UInt8)) : wsStop G 1 := by
  have hbs : G.bs = [97, 32] := h.bs
  simp only [wsStop, wsX, wsByte, hbs, List.getD]
  decide

/-- **The entry's own byte is a token byte.**  `wsCont G 0` holds at the letter: the run
starts at the entry and advances over `97`. -/
theorem spaceByte_start_cont {m0 : Mem} (G : WalkGeom m0) (h : TrailingSpaceDocument G
    (97 : UInt8)) : wsCont G 0 := by
  have hbs : G.bs = [97, 32] := h.bs
  simp only [wsCont, wsX, wsByte, hbs, List.getD]
  decide

/-- **The stop is the second byte, not the first.**  `wsStop G 0` is false at the letter:
the byte before the entry's end — the space at index one — is the run's stop, and the
entry's own byte is what the run advances over.  So the class is about the document's
second byte, and this is the detector that separates the two. -/
theorem spaceByte_stop_not_entry {m0 : Mem} (G : WalkGeom m0) (h : TrailingSpaceDocument G
    (97 : UInt8)) : ¬ wsStop G 0 := by
  have hbs : G.bs = [97, 32] := h.bs
  simp only [wsStop, wsX, wsByte, hbs, List.getD]
  decide

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.runLastHead_a
#print axioms LeanLLVM.Refinement.WalkScope.runLastClass_a
#print axioms LeanLLVM.Refinement.WalkScope.runLastPrem_a
#print axioms LeanLLVM.Refinement.WalkScope.runLastFacts_byte
#print axioms LeanLLVM.Refinement.WalkScope.run_last_arm
#print axioms LeanLLVM.Refinement.WalkScope.run_last_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.spaceVisits_le
#print axioms LeanLLVM.Refinement.WalkScope.spaceNotSpanStart
#print axioms LeanLLVM.Refinement.WalkScope.spaceByte_stop
#print axioms LeanLLVM.Refinement.WalkScope.spaceByte_start_cont
#print axioms LeanLLVM.Refinement.WalkScope.spaceByte_stop_not_entry

end WalkScope
end LeanLLVM.Refinement
