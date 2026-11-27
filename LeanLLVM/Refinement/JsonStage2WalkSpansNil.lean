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
`wordBytes 8 0` (`walkFinishMemAccept_ndst_zero_of_spans_nil`).  The evidence and
emission theorems take the returned memory at the four reads that the emission
consumes (`JsonWalkReads`) in place of the arena datum, so the remaining premise is
the identification of the pipeline run's return with the walk's accept route — the
stage-2 body link, not an arena fact.

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

/-! ### The returned memory, named at its four reads

`evb_emission_of_bracket_walk` (`JsonStage2WalkSpansChain.lean:393`) takes `[1]`'s
emission from the walk's own accept route.  It used to be stated against one memory
equation towards that: `hmem : m = walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen`,
the accept finalisation's two cursor stores over the loop's last memory
(`JsonStage2WalkTargetPost.lean:123`).

That equation is stronger than what the emission reads, and no frame supplies it:
`UnchangedOutside mem m R` is a pointwise equality *outside* the union of `R`
(`CallsFootprint.lean:45`), so it is silent inside the list — a write inside a
listed region keeps the frame and moves the memory (`frame_not_identifying`,
`JsonNumFastSpine.lean`) — and the report's list is not the walk's, so the frame the
scan's post carries cannot be narrowed to the walk's spine either
(`reportFrame_not_walkWideAt`, same module).

So the interface is stated at what the emission actually reads, and at nothing
wider.  `JsonWalkReads` names the returned memory by four reads — the two cursor
words at the carried lengths and the two payload buffers at those lengths — and
`jsonWalkReads_of_mem` proves the four follow from the accept finalisation.  The
equation therefore keeps one use here, as the producer of the reads; every consumer
downstream names the reads and no whole memory. -/

/-- **The accept route's returned memory, read at the four fields the emission
consumes.**

* `ndst` is the `%ndst` cursor word the finalisation stores, `wordBytes 8 C.alen`;
* `nev` is the `%nev` cursor word, `wordBytes 8 C.evlen`;
* `arena` is the arena buffer at `G.dst` for the carried arena length `C.alen`;
* `ev` is the event buffer at `G.ev` for the carried event length `C.evlen`.

The payload fields are `HasBytes`, the tree's region read (`∃ bs, readBytes … =
some bs`), because the emission's conclusion binds the bytes existentially.  The
structure names no memory and no base memory: a caller that has any memory reading
these four ways has all the interface gives.

It is a value and not a theorem of the scan.  The scan's run theorem concludes
`∃ v m, runFuel … = some (.ret v m)` (`Stage2WalkCompletes`,
`JsonStage2Body.lean:1747`; `stage2_walk_yields_record`, `:3512`), so the memory
is existentially bound; the post's whole-memory clauses are four read-backs,
presence, and the frame at `stage2ReportFrame` (`stage2Boundary`,
`JsonStage2Contract.lean:1137`; its frame clause at `:1227`).  A frame is silent
inside its own list (`UnchangedOutside`, `CallsFootprint.lean:45`), so it cannot
pin a memory, and the list it is stated at is wider than the walk's in the arena
and event extents, so it cannot be narrowed to the walk's either.  The tree names
the memory where it proves the boundary — `walkFinishPost_accept`
(`JsonStage2WalkTargetPost.lean:985`) — but the boundary hides it under the same
existential; what survives is these four reads. -/
structure JsonWalkReads {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (m : Mem) : Prop where
  /-- The `%ndst` cursor word the accept finalisation stores. -/
  ndst : readBytes m G.ndst 8 = some (wordBytes 8 C.alen)
  /-- The `%nev` cursor word the accept finalisation stores. -/
  nev : readBytes m G.nev 8 = some (wordBytes 8 C.evlen)
  /-- The arena buffer at the carried arena length. -/
  arena : HasBytes m G.dst C.alen
  /-- The event buffer at the carried event length. -/
  ev : HasBytes m G.ev C.evlen

/-- **The arena and event extents are separate from the two cursor slots.**  The
staging's `DisjointRegions` (`WalkGeom.separate`) names the arena's reserve and the
event stream's capacity before the two slots, so each payload extent misses both
stores the accept finalisation makes. -/
theorem stage2Regions_payload_outside {b n ep nep xp nxp dst ndst0 ev evcap ndst nev
    err : Nat}
    (h : DisjointRegions (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev
      err)) :
    (dst + (ndst0 + n + stage2ArenaReserve) ≤ ndst ∨ ndst + 8 ≤ dst) ∧
      (dst + (ndst0 + n + stage2ArenaReserve) ≤ nev ∨ nev + 8 ≤ dst) ∧
      (ev + evcap ≤ ndst ∨ ndst + 8 ≤ ev) ∧
      (ev + evcap ≤ nev ∨ nev + 8 ≤ ev) := by
  simp only [DisjointRegions, stage2Regions] at h
  simp only [List.pairwise_cons, List.Pairwise.nil, and_true] at h
  obtain ⟨-, -, -, hdst, hev, -, -, -⟩ := h
  have h1 := hdst (ndst, 8) (by simp)
  have h2 := hdst (nev, 8) (by simp)
  have h3 := hev (ndst, 8) (by simp)
  have h4 := hev (nev, 8) (by simp)
  simpa using ⟨h1, h2, h3, h4⟩

/-- **The four reads follow from the accept finalisation.**  Given the memory
equation `m = walkFinishMemAccept G s.mem C.alen C.evlen` and the walk's invariant
at the final state, `m` reads the two cursor words and both payloads.  The payload
reads are the walk's own (the invariant's `owned` presence at the staged extents,
narrowed to the carried lengths), carried across the two stores by
`stage2Regions_payload_outside`. -/
theorem jsonWalkReads_of_mem {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} (hInv : WalkInv G C s)
    (hmem : m = walkFinishMemAccept G s.mem C.alen C.evlen) :
    JsonWalkReads G C m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmem]
    exact walkFinishMemAccept_ndst G (walkFinish_sep G C).1
  · rw [hmem]
    exact walkFinishMemAccept_nev G
  · obtain ⟨aLong, haLong⟩ :=
      hInv.owned (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp [walkStaged])
    have halen_le : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve := by
      have := WalkInv.alen_le hInv
      omega
    have hshort : readBytes s.mem G.dst C.alen = some (aLong.take C.alen) :=
      readBytes_take_prefix halen_le haLong
    obtain ⟨houtN, houtV, -, -⟩ := stage2Regions_payload_outside G.separate
    refine ⟨aLong.take C.alen, ?_⟩
    rw [hmem, walkFinishMemAccept,
      walkReadBytes_writeBytes_outside (start := G.nev) (addr := G.dst) (n := C.alen)
        (v := wordBytes 8 C.evlen) ?_,
      walkReadBytes_writeBytes_outside (start := G.ndst) (addr := G.dst) (n := C.alen)
        (v := wordBytes 8 C.alen) ?_]
    · exact hshort
    · rcases houtN with h | h
      · exact Or.inl (le_trans (Nat.add_le_add_left halen_le G.dst) h)
      · exact Or.inr (by rw [wordBytes, natToBytes_length]; exact h)
    · rcases houtV with h | h
      · exact Or.inl (le_trans (Nat.add_le_add_left halen_le G.dst) h)
      · exact Or.inr (by rw [wordBytes, natToBytes_length]; exact h)
  · obtain ⟨eLong, heLong⟩ :=
      hInv.owned (G.ev, G.evcap) (by simp [walkStaged])
    have hevlen_le : C.evlen ≤ G.evcap :=
      le_trans (WalkInv.evlen_le hInv) G.evRoom
    have hshort : readBytes s.mem G.ev C.evlen = some (eLong.take C.evlen) :=
      readBytes_take_prefix hevlen_le heLong
    obtain ⟨-, -, houtN, houtV⟩ := stage2Regions_payload_outside G.separate
    refine ⟨eLong.take C.evlen, ?_⟩
    rw [hmem, walkFinishMemAccept,
      walkReadBytes_writeBytes_outside (start := G.nev) (addr := G.ev) (n := C.evlen)
        (v := wordBytes 8 C.evlen) ?_,
      walkReadBytes_writeBytes_outside (start := G.ndst) (addr := G.ev) (n := C.evlen)
        (v := wordBytes 8 C.alen) ?_]
    · exact hshort
    · rcases houtN with h | h
      · exact Or.inl (le_trans (Nat.add_le_add_left hevlen_le G.ev) h)
      · exact Or.inr (by rw [wordBytes, natToBytes_length]; exact h)
    · rcases houtV with h | h
      · exact Or.inl (le_trans (Nat.add_le_add_left hevlen_le G.ev) h)
      · exact Or.inr (by rw [wordBytes, natToBytes_length]; exact h)

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

/-- **The arena datum at the interface's `%ndst` read.**  The emission's `%ndst`
word follows from the four reads, the merge state's empty span list, the zero
staging and the slot's identification.  The word is read out of the interface's
`ndst` field at `C.alen`, and `C.spans = []` collapses the carried length to the
staged cursor, which the zero staging makes zero. -/
theorem walk_accept_ndst_zero_of_reads {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} (h : JsonWalkReads G C m) (hndstG : G.ndst = evbLayout.ndst)
    (hInv : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0)) :
    readBytes m evbLayout.ndst 8 = some (wordBytes 8 0) := by
  have halen : C.alen = G.ndst0 := WalkInv.alen_eq_ndst0_of_spans_nil hInv hspans
  have h0 : G.ndst0 = 0 := ndst0_eq_zero_of_staged_zero G hstaged
  have hword : wordBytes 8 C.alen = wordBytes 8 0 := by rw [halen, h0]
  rw [← hndstG, ← hword]
  exact h.ndst

/-- **The arena datum at the run's accept memory.**  The pipeline's returned
memory is the walk's accept route's (`hmem`), its `%ndst` slot is the route's
(`hndstG`), and the merge state reserved nothing: the datum `evb_evidence_of_spec`
takes holds.  This is `walk_accept_ndst_zero_of_reads` at the reads the equation
produces (`jsonWalkReads_of_mem`); it is the equation's own form of the datum, kept
beside the narrow one rather than on the release path. -/
theorem walk_accept_ndst_zero {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {m : Mem} (hndstG : G.ndst = evbLayout.ndst)
    (hInv : WalkInv G C s) (hspans : C.spans = [])
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0))
    (hmem : m = walkFinishMemAccept G s.mem C.alen C.evlen) :
    readBytes m evbLayout.ndst 8 = some (wordBytes 8 0) :=
  walk_accept_ndst_zero_of_reads (jsonWalkReads_of_mem hInv hmem) hndstG hInv hspans
    hstaged

/-- **The evidence with no arena premise at the walk.**  `evb_evidence_of_spec`
takes the returned cursor word; here it follows from the merge state's empty span
list, the zero staging, and the identification of the run's memory with the accept
route's.  This is the equation's own form of the evidence: `walk_accept_ndst_zero`
converts `hmem` through `jsonWalkReads_of_mem`, so the statement is available beside
the narrow route rather than on it. -/
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

/-- **The emission with no arena premise at the walk and no whole memory.**
`evb_emission_of_spec` at the arena datum the returned memory's `%ndst` read gives:
the same conclusion, its datum derived from the merge state's `C.spans = []`.  The
memory enters as `JsonWalkReads`, so no equation between whole memories is named. -/
theorem evb_emission_of_walk_accept {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
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
  evb_emission_of_spec hpre hext hspec
    (walk_accept_ndst_zero_of_reads h hndstG hInv hspans hstaged)

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

/-- info: 'LeanLLVM.Refinement.WalkScope.JsonWalkReads' does not depend on any axioms -/
#guard_msgs in
#print axioms JsonWalkReads

/-- info: 'LeanLLVM.Refinement.WalkScope.stage2Regions_payload_outside' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Regions_payload_outside

/-- info: 'LeanLLVM.Refinement.WalkScope.jsonWalkReads_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms jsonWalkReads_of_mem

/-- info: 'LeanLLVM.Refinement.WalkScope.walk_accept_ndst_zero_of_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walk_accept_ndst_zero_of_reads

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
