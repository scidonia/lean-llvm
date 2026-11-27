/-
# The number path's write spine: why four reads, and not a memory

`evb_emission_of_bracket_walk` (`JsonStage2WalkSpansChain.lean:393`) takes `[1]`'s
emission from the walk's own accept route, at the four reads `JsonWalkReads` names
(`JsonStage2WalkSpansNil.lean`) rather than at a whole memory.  This module is the
argument for that shape.  The equation it replaced was
`hmem : m = walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen`, the accept finalisation's
two cursor stores over the loop's last memory (`JsonStage2WalkTargetPost.lean:123`).

That equation is stronger than the emission reads, and no frame supplies it:
`UnchangedOutside mem m R` is a pointwise equality *outside* the union of `R`
(`CallsFootprint.lean:45`), so it is silent inside the list.  Two consequences are
proved here rather than asserted:

* **A frame cannot identify a memory.**  A write inside a listed region leaves the
  frame true and changes the memory (`frame_not_identifying`), so no frame,
  however wide, can give an equation of whole memories.
* **The scan's frame is not even the walk's.**  The report's arena entry is
  `(dst, ndst' + stage2ArenaReserve)` (`stage2Writes`, `JsonStage2Contract.lean:350`)
  and the walk's is `(G.dst, C.alen)`.  At the accept route the reserved extent is
  the carried cursor (`stage2BoundaryAt_of_accept`'s `U_le_ndst`,
  `JsonStage2WalkTargetPost.lean:767`), so the two lists differ by the decoder's
  64-byte slack alone: the report's list covers bytes the walk's leaves out, and
  the frame at it does not restrict the walk's list
  (`frame_weaker_not_stronger`, `reportFrame_not_walkWideAt`).  The containment
  runs the other way, which is why the tree states the walk's frame *transfers to*
  the report's (`UnchangedOutside.of_covered`, `JsonStage2Contract.lean:774`).

## Where the interface lives

`JsonWalkReads` — the returned memory at the two cursor words and the two payloads —
and its builder `jsonWalkReads_of_mem` are declared in `JsonStage2WalkSpansNil`, the
lowest module the seam (`JsonStage2WalkSpansChain`) can name.  `jsonWalkReads_of_mem`
proves the four reads follow from the accept finalisation, so the equation keeps one
use there, as the producer of the reads; the emission the chain calls takes the
reads and names no whole memory.

## The scan's run theorem and the memory it concludes

* **The run theorem.**  `Stage2WalkObligation` (`JsonStage2Body.lean:3495`) is the
  scan's obligation; `stage2_walk_yields_record` (`:3512`) is its consumer at the
  ABI's arguments, and `Stage2WalkCompletes` (`:1747`) is the completion conjunct
  it is equivalent to (`stage2WalkObligation_iff_completion`, `:3541`).
* **The memory it concludes.**  `∃ v m, runFuel (stage2Calls stage2SubCalls)
  (stage2Budget …) stage2Body … = some (.ret v m)` — the returned memory `m` is
  bound by the existential and never named.  The walk's own loop reaches the same
  shape one level down: `WalkTargetPost` (`JsonStage2WalkTraverse.lean:670`) and
  its terminal disjunct bind `m` existentially, and the producers that *prove* it
  (`walkFinishPost_accept`, `JsonStage2WalkTargetPost.lean:985`;
  `stage2Boundary_of_accept`, `:777`) know the memory is `walkFinishMemAccept` and
  conclude `stage2Boundary` at it — under the same existential, so the equation is
  not projectable from the conclusion.  The terminal constructor therefore has the
  witness and must preserve its reads; a consumer behind the frame cannot rebuild
  them.

The interface is route-level rather than per number token: it is the `[1]` walk's
returned memory, one value beside the number-conversion assumption
`JsonNumFastAssumed` and not a field of it — a per-token structure would carry the
same walk-level reads once per token, and its parameters (`bs d i0 d0 n`) do not
name a geometry, a carry or a state.
-/
import LeanLLVM.Refinement.JsonStage2WalkSpansChain

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.WalkScope

/-! ### A frame is silent inside its own list

Two memories, one frame: a write inside a listed region keeps the frame and moves
the memory.  So no frame is a memory, and no equation of whole memories follows
from one.  This is why the interface had to be the returned memory's four reads and
could not be a frame. -/

/-- **A frame does not identify its memory.**  A write at a byte inside one of the
frame's regions leaves the frame true and gives a different memory: the frame is a
claim about the complement of the list, and says nothing about the list's own
bytes. -/
theorem frame_not_identifying {mem m : Mem} {R : List (Nat × Nat)} {a : Nat} {x : UInt8}
    (h : UnchangedOutside mem m R)
    (hin : ∃ q ∈ R, q.1 ≤ a ∧ a + 1 ≤ q.1 + q.2)
    (hx : readByte m a ≠ some x) :
    ∃ m' : Mem, m' ≠ m ∧ UnchangedOutside mem m' R := by
  refine ⟨writeBytes m a [x], ?_, h.write_le hin (bs := [x]) (w := 1) (by simp)⟩
  intro hEq
  refine hx ?_
  rw [← hEq]
  simpa using readByte_writeBytes_at m [x] a 0 (by simp)

/-- **A frame at a wider list does not give one at a narrower list.**  When a byte
lies inside a region of the wider list and outside every region of the narrower
one, a write at it keeps the first frame and breaks the second: strengthening a
frame is not a consequence of having one, however much the two lists' *ranges*
overlap in the other direction. -/
theorem frame_weaker_not_stronger {mem : Mem} {R R' : List (Nat × Nat)} {a : Nat}
    {x : UInt8}
    (hin : ∃ q ∈ R', q.1 ≤ a ∧ a + 1 ≤ q.1 + q.2)
    (hout : ∀ r ∈ R, ¬ (r.1 ≤ a ∧ a < r.1 + r.2))
    (hx : readByte mem a ≠ some x) :
    ∃ m : Mem, UnchangedOutside mem m R' ∧ ¬ UnchangedOutside mem m R := by
  refine ⟨writeBytes mem a [x], (UnchangedOutside.refl' mem R').write_le hin
    (bs := [x]) (w := 1) (by simp), ?_⟩
  intro hfr
  have hEq : readByte (writeBytes mem a [x]) a = readByte mem a := hfr a hout
  have hw : readByte (writeBytes mem a [x]) a = some x := by
    simpa using readByte_writeBytes_at mem [x] a 0 (by simp)
  rw [hw] at hEq
  exact hx hEq.symm

/-- **The scan's frame is not the walk's write spine.**  At the report's region
list and the walk's, a byte in the first and outside the second witnesses that the
frame the scan's post carries is not a frame over the list the walk's invariant is
stated at: `stage2ReportFrame`'s arena entry reaches `ndst' + stage2ArenaReserve`
while `walkWideAt`'s reaches the carried `C.alen ≤ ndst'`, so the containment the
tree proves (`UnchangedOutside.of_covered`, walk's frame to report's) does not run
backwards. -/
theorem reportFrame_not_walkWideAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {nextEnd ndst' nev' a : Nat} {x : UInt8}
    (hin : ∃ q ∈ stage2ReportFrame G.dst ndst' G.ev nev' G.ndst G.nev G.err
      C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e
      C.stage.d G.next0 nextEnd, q.1 ≤ a ∧ a + 1 ≤ q.1 + q.2)
    (hout : ∀ r ∈ walkWideAt G C (nextEnd - G.next0), ¬ (r.1 ≤ a ∧ a < r.1 + r.2))
    (hx : readByte m0 a ≠ some x) :
    ∃ m : Mem,
      UnchangedOutside m0 m (stage2ReportFrame G.dst ndst' G.ev nev' G.ndst G.nev
        G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z
        C.stage.e C.stage.d G.next0 nextEnd) ∧
      ¬ UnchangedOutside m0 m (walkWideAt G C (nextEnd - G.next0)) :=
  frame_weaker_not_stronger hin hout hx

/-! ### The interface at the emission

`evb_emission_of_walk_accept` (`JsonStage2WalkSpansNil.lean`) is the emission at
these four reads: it turns the interface's `ndst` field into the arena datum the
emission reads, which `C.spans = []` and a zero-staged slot make zero.  The name
below is the one the assumption section publishes for that conclusion; the proof is
the accept route's, so the two cannot drift apart. -/

/-- **`[1]`'s emission from the four reads.**  `evb_emission_of_spec` needs one
read of the returned memory: its `%ndst` word, zero at this staging.  That is the
interface's `ndst` field at `C.alen = 0`; the remaining three conjuncts are the
run's own report (`hext`) and the specification post at `m` (`hspec`), which the
emission theorem already takes.  No whole memory is named. -/
theorem evb_emission_of_walk_spine {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} {next ndstU nev' : Nat}
    (h : JsonWalkReads G C m)
    (hpre : routePre evbLayout evbDoc)
    (hndstG : G.ndst = evbLayout.ndst)
    (hInv : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0))
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hspec : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m)) :
    ∃ (arena evs : List UInt8),
      readBytes m evbLayout.ndst 8 = some (wordBytes 8 ndstU) ∧
      readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
      readBytes m evbLayout.dst ndstU = some arena ∧
      readBytes m evbLayout.ev nev' = some evs ∧
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evs) (ByteString.literal arena)).bind valueOfEvents =
        scalarCanonValueOfBytes evbDoc ∧
      Nonempty EvbCertificate :=
  evb_emission_of_walk_accept h hpre hndstG hInv hspans hstaged hext hspec

/-! ### Axiom footprints

`#print axioms` under `#guard_msgs`, so the build checks each footprint rather than
printing it.  The emission carries `Classical.choice` from `evb_emission_of_spec`'s
route (`JsonEventEmission.lean`), whose pin carries the same carrier; nothing in
this module introduces it. -/

/-- info: 'LeanLLVM.Refinement.frame_not_identifying' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frame_not_identifying

/-- info: 'LeanLLVM.Refinement.frame_weaker_not_stronger' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frame_weaker_not_stronger

/-- info: 'LeanLLVM.Refinement.reportFrame_not_walkWideAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reportFrame_not_walkWideAt

/-- info: 'LeanLLVM.Refinement.evb_emission_of_walk_spine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_emission_of_walk_spine

end LeanLLVM.Refinement
