/-
# The span list at the merge: the one writer, the four carries, and the word it leaves

The release's last premise is the arena cursor the walk reports at `[1]`:

```lean
readBytes m evbLayout.ndst 8 = some (wordBytes 8 0)
```

`JsonStage2WalkArenaWord` reduced it to the merge state's span list: with
`C.spans = []` the finalisation's accept route copies the staged cursor, and a
staging whose slot is zero leaves `wordBytes 8 0` (`arenaWord_zero_of_spans_nil`).
What was missing is `C.spans = []` itself.  This module does three things:

* it records the **census of the span list's writers** at the carries the dispatch
  actually builds: the string arm's reservation appends
  (`strC₉`, `JsonStage2WalkDispatchWitnessString:570`), and the opener's, the
  scalar's and the closer's merge carries keep the source's list
  (`openC₉`, `scMergeC`, `closeCEnd`, all `{ … with … }` updates).  The seed is
  `walkSeed`/`walkCarryZero`'s `[]`;
  it states the **clause the boundary would need** and the arm that refuses it:
  `G.nxp = 0 → C.spans = []` is not a fact about the walk, because the string arm
  reserves for *every* string, escaped or not — `%nxp` enters
  `WalkLink.z_arena_reserve_exit` only as a call argument, and the arm's target
  carry appends unconditionally (`strC₉_spans`).  The refusing arm is the string
  arm; at `[1]`, whose document has no string token, the arm is simply not
  reached;
* it composes the three non-string carries into the merge (`spans_nil_of_three_arms`):
  if the run's merge carry is the opener's, then the number's, then the closer's,
  a seed with `[]` has `[]` at `cleanup478.i`.  That is the strongest statement
  available without the run itself: the equation between the run's carries and
  these abbreviations is what the concrete `[1]` composition still owes.

The last section closes the arena premise at the accept route's memory: from the
merge state's `C.spans = []` and a zero-staged cursor, the returned `%ndst` word is
`wordBytes 8 0` (`walkFinishMemAccept_ndst_zero_of_spans_nil`).  The two evidence
theorems take that memory equation (`m = walkFinishMemAccept …`) in place of the
arena datum, so the remaining premise is the identification of the pipeline run's
return with the walk's accept route — the stage-2 body link, not an arena fact.

## The search

`grep -rn "spans :=" LeanLLVM/Refinement` returns exactly the seed (`walkSeed`,
`walkCarryZero`) and the reserve (`JsonStage2WalkDispatchWitnessString:570`,
`JsonStage2StringStageFacts:256`, the same update written twice).  No other
statement writes the field, so no arm besides the string reserve extends the list.
`grep -rn "\.spans"` over the development returns only `WalkInv`'s five accounting
clauses (`alen_le_sum`, `alen_ge`, `spans_order`, `spans_inside`, `spans_end`),
`alen_eq_ndst0_of_spans_nil`, and the zero-carry lemmas — no clause mentions the
list's *content* against the document, `G.ent`, `G.nxp`/`G.xp`, `C.events`,
`WalkTraceRow` or `WalkAlign`.  An `exact?` on the merge-state goal `C.spans = []`
finds nothing, as expected: the goal is not a consequence of `WalkInv` alone, and
the only arm whose carry changes the list is the one at a string token.
-/
import LeanLLVM.Refinement.JsonStage2WalkArenaWord
import LeanLLVM.Refinement.JsonStage2WalkTargetPost
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpeners
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosers
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar
import LeanLLVM.Refinement.JsonEventEmission

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The census

The four merge carries at `cleanup478.i`, one per head-switch class the `[1]` walk
takes: the opener's, the scalar (number/literal) arm's, the closer's, and the
string arm's.  The first three are record updates that leave `spans` alone; the
string arm's reservation is the only one that appends. -/

/-- **The opener's merge carries the source's span list.**  `openC₉` is `{ C with
… }` over the block, the stack maps and the event cursor; the arena accounting is
untouched. -/
theorem openC₉_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉ C b).spans = C.spans := rfl

/-- **The scalar arm's merge carries the source's span list.**  `scMergeC` is the
tail's carry (`TailCarryEnd` over the head chain, every step a `{ C with … }`
update) with its block moved to `cleanup478.i`; no step writes `spans`. -/
theorem scMergeC_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (ev : EventRecord) : (scMergeC C ev).spans = C.spans := rfl

/-- **The closer's merge carries the source's span list.**  `closeCEnd` moves the
block, the event cursor and the trace; the arena accounting is the source's. -/
theorem closeCEnd_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) (c8 : BitVec 8) : (closeCEnd C spz c8).spans = C.spans := rfl

/-- **The string arm's reservation appends one window.**  This is the one carry
update in the walk that changes the list (`strC₉` at
`JsonStage2WalkDispatchWitnessString:570`); the appended pair is the cursor before
the reservation and the entry's extent, which is `z_arena_reserve.exit`'s own
`C.alen + ext`. -/
theorem strC₉_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) : (strC₉ C ix ext).spans = C.spans ++ [(C.alen, ext)] := rfl

/-- **The reservation also moves the cursor by the window.**  Stated beside
`strC₉_spans` so the pair reads as the one update it is: `alen` and `spans` move
together, and nothing else in the carry does. -/
theorem strC₉_alen {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ix : BitVec 64)
    (ext : Nat) : (strC₉ C ix ext).alen = C.alen + ext := rfl

/-- **The advertised clause's refusing arm.**  If the source carry has no span, the
string arm's reservation leaves exactly the one window, regardless of anything about
the escape count: `strC₉` does not mention `G.nxp`.  So an invariant of the form
`G.nxp = 0 → C.spans = []` is false at the string arm's target, and no proof of it
can exist while that arm is in the dispatch. -/
theorem strC₉_spans_ne_nil {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (ix : BitVec 64) (ext : Nat) (h : C.spans = []) :
    (strC₉ C ix ext).spans = [(C.alen, ext)] := by
  rw [strC₉_spans, h, List.nil_append]

/-- **The non-string arms compose to the empty list.**  If the run's merge carry is
the opener's, then the scalar arm's, then the closer's, and the seed carry has no
span, the merge's list is empty.  This is the `[1]` chain's span half: three
revolutions, none of them a string, and the field never moves.

The three equations are what the concrete composition supplies: each arm's segment
lemma at `cleanup478.i` names its target carry (`openC₉`/`scMergeC`/`closeCEnd`), and
the header pass between them is a `{ C with … }` too.  What is still owed is the
state-level chain itself — the seed at `[1]`'s staging, the three segments and the
finish — not any fact about the list. -/
theorem spans_nil_of_three_arms {m0 : Mem} {G : WalkGeom m0}
    {C₀ C₁ C₂ C₃ : WalkCarry G} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8}
    (h₁ : C₁ = openC₉ C₀ b) (h₂ : C₂ = scMergeC C₁ ev)
    (h₃ : C₃ = closeCEnd C₂ spz c8) (h₀ : C₀.spans = []) : C₃.spans = [] := by
  rw [h₃, h₂, h₁, closeCEnd_spans, scMergeC_spans, openC₉_spans, h₀]

/-! ### The word the accept route leaves

With `C.spans = []` the merge state's logged cursor is the staged one and the
staging's zero makes that zero.  The accept route's copy writes that word at the
caller's `%ndst`, so the returned memory's slot reads `wordBytes 8 0` — the arena
datum `evb_evidence_of_spec` takes. -/

/-- **The accept route's `%ndst` word at a walk with no reserved span.**  The copy
loads the log's arena word (`walkFinishMemAccept`'s first store, from the
finalisation's `a = C.alen`), and `C.spans = []` collapses `C.alen` to `G.ndst0`
(`WalkInv.alen_eq_ndst0_of_spans_nil`), which a zero-staged slot makes zero. -/
theorem walkFinishMemAccept_ndst_zero_of_spans_nil {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (h : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0)) :
    readBytes (walkFinishMemAccept G s.mem C.alen C.evlen) G.ndst 8 =
      some (wordBytes 8 0) := by
  have halen : C.alen = G.ndst0 := WalkInv.alen_eq_ndst0_of_spans_nil h hspans
  have h0 : G.ndst0 = 0 := ndst0_eq_zero_of_staged_zero G hstaged
  have hsep := (walkFinish_sep G C).1
  have hw := walkFinishMemAccept_ndst G (m := s.mem) (a := C.alen) (l := C.evlen) hsep
  -- Rewrite the word alone: matching `C.alen` under `readBytes` would unfold the
  -- memory functions and exhaust the heartbeats.
  have hword : wordBytes 8 C.alen = wordBytes 8 0 := by rw [halen, h0]
  rw [hword] at hw
  exact hw

/-- **The arena datum at the run's accept memory.**  The pipeline's returned
memory is the walk's accept route's (`hmem`), its `%ndst` slot is the route's
(`hndstG`), and the merge state reserved nothing: the datum `evb_evidence_of_spec`
takes holds.  This is the `C.spans = [] → hndst` step, with the run's memory named
rather than assumed. -/
theorem walk_accept_ndst_zero {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} (hndstG : G.ndst = evbLayout.ndst)
    (hInv : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0))
    (hmem : m = walkFinishMemAccept G s.mem C.alen C.evlen) :
    readBytes m evbLayout.ndst 8 = some (wordBytes 8 0) := by
  have hw := walkFinishMemAccept_ndst_zero_of_spans_nil hInv hspans hstaged
  rw [hmem, ← hndstG]
  exact hw

/-- **The evidence with no arena premise at the walk.**  `evb_evidence_of_spec`
takes the returned cursor word; here it follows from the merge state's empty span
list, the zero staging, and the identification of the run's memory with the accept
route's.  The arena half of the release's last premise is gone; what remains is
`hmem`, the stage-2 call's return being the walk's finalisation. -/
theorem evb_evidence_of_walk_accept {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} {next ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hndstG : G.ndst = evbLayout.ndst)
    (hInv : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0))
    (hmem : m = walkFinishMemAccept G s.mem C.alen C.evlen)
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hspec : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m)) :
    Stage2OutcomeEvidence evbLayout.base evbArgs evbMem ndstU nev'
      (.ret (some (.int 64 1)) m) :=
  evb_evidence_of_spec hpre hext hspec
    (walk_accept_ndst_zero hndstG hInv hspans hstaged hmem)

/-- **The emission with no arena premise at the walk.**  `evb_emission_of_spec` at
`evb_evidence_of_walk_accept`: the same conclusion, its arena datum derived from
the merge state's `C.spans = []`. -/
theorem evb_emission_of_walk_accept {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} {next ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hndstG : G.ndst = evbLayout.ndst)
    (hInv : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0))
    (hmem : m = walkFinishMemAccept G s.mem C.alen C.evlen)
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
  evb_emission_of_spec hpre hext hspec
    (walk_accept_ndst_zero hndstG hInv hspans hstaged hmem)

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.WalkScope.openC₉_spans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.openC₉_spans

/-- info: 'LeanLLVM.Refinement.WalkScope.scMergeC_spans' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.scMergeC_spans

/-- info: 'LeanLLVM.Refinement.WalkScope.closeCEnd_spans' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.closeCEnd_spans

/-- info: 'LeanLLVM.Refinement.WalkScope.strC₉_spans' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.strC₉_spans

/-- info: 'LeanLLVM.Refinement.WalkScope.strC₉_spans_ne_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.strC₉_spans_ne_nil

/-- info: 'LeanLLVM.Refinement.WalkScope.spans_nil_of_three_arms' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.spans_nil_of_three_arms

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishMemAccept_ndst_zero_of_spans_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishMemAccept_ndst_zero_of_spans_nil

/-- info: 'LeanLLVM.Refinement.WalkScope.walk_accept_ndst_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walk_accept_ndst_zero

/-- info: 'LeanLLVM.Refinement.WalkScope.evb_evidence_of_walk_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.evb_evidence_of_walk_accept

/-- info: 'LeanLLVM.Refinement.WalkScope.evb_emission_of_walk_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.evb_emission_of_walk_accept

end WalkScope
end LeanLLVM.Refinement
