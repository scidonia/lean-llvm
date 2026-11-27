/-
# The caller's result at `[1]`, from the walk's execution

`evb_run_to_emission` (`JsonEventEmission`) states the emission given the
*accepting* run: its `hrun` fixes the verdict word to `1`, and its `hspec`,
`hndst` and `hext` carry the post, the arena word and the extents.  This module
derives that accepting return and the caller-visible reads from the walk's own
execution, so the verdict, the output bytes, the cursor and the parser's answer
are all conclusions and none of them a hypothesis.

# What is assumed

Three groups, each an environment or ABI fact, and nothing about the result:

1. **The caller's staging and the call's layout.**  `hpre : routePre evbLayout
   evbDoc` is the adapter's staging of `[1]` at `evbLayout` (`routeArgs`'s twenty
   arguments); `hstageWord : readBytes m0 G.ndst 8 =
   readBytes evbMem evbLayout.ndst 8` is that the walk's base memory stages the
   same cursor word the adapter staged (zero, through `hpre`); and
   `hndstG`/`hnevG`/`hdstG`/`hevG`/`hnev0` say the stage-2 unit's
   own buffers are the caller's: the walk's arena, event and
   cursor addresses are `evbLayout`'s, and the event stream starts at the staged
   cursor (`G.nev0 = 0`).  This is *which layout*: the emitted stage-2 unit's
   thirteen-argument ABI at the addresses the pipeline stages.
2. **The execution.**  The five counted segments — the opener's, the two
   revolutions, the number's and the closer's — with the carry identifications
   the dispatch exposes, plus the two tag bytes (`hb3`, `hc8`) and the numeral's
   record (`hevRec`).  `hevRec` is the *callee* assumption, not an output byte:
   the stage-2 unit's `num_fast_el1` slot answers with `strtodSpec`'s bits of the
   document's numeral, which at `[1]` is `evbBits` by definition.  Which callee:
   `stage2Calls stage2SubCalls`'s model of the number path.
3. **The merge's exit selection.**  The registers and `phi` operands the accept
   block reads at the merge state `s₃`, and the merge's two tests (`hsp0`: the
   nesting depth is zero; `hroot0`: the root is complete).  These are *state*
   facts — the run's own depth and root-done words — and they select the
   finalisation's accept route.  The verdict is not among them: it is read off
   the route's execution below.

# What is derived

* the composed run `s₀ → s₃` (the five segments) and `s₃ → return` (the accept
  route), returning `some (.ret (some (.int 64 1)) …)`: the **accepting
  verdict**, from `walkFinishPost_accept`, whose statement now pins both the
  verdict and the returned memory;
* the returned memory's four reads (`JsonWalkReads`, the walk's interface),
  rebuilt from the accept finalisation by `jsonWalkReads_of_mem`;
* the arena cursor `0` (`C.alen = G.ndst0 = 0`, from the merge's empty span list
  and the staged zero) and the event extent `evbEvents.length`;
* the event bytes `evbEvents` — the walk's trace is `evbRecords` (the carries'
  own `events` fields), and `WalkInv.evBytes` reads the stream at the carried
  cursor;
* the canonical value, by the closed slice theorem `evb_sliceOne_value_closed`
  after the indexed reader agrees with `eventsOfBytes` (`eventsOfBytesIndexedAgrees`);
* the certificate, naming the linked symbol, object, adapter and ABI.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonStage2WalkSpansChain
import LeanLLVM.Refinement.JsonStage2WalkTargetPost
import LeanLLVM.Refinement.JsonStage2WalkRowSteps
import LeanLLVM.Refinement.JsonEventEmission
import LeanLLVM.Refinement.JsonEventPremisesOneParse

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonPipelineIR

/-! ### The record trace at `[1]`

The five merge carries' `events` fields compose to `evbRecords`: the opener
appends the bracket's tag, the number's merge appends the numeral's record, and
the closer appends the bracket's closing tag, with the two intermediate head
passes leaving the list alone.  The three inputs `[1]` fixes are the document's
two tag bytes and the numeral's record. -/

/-- **`[1]`'s trace, from the five carries.**  With the opener's tag `3`, the
number's record and the closer's tag `4`, the seed's empty list ends at
`evbRecords`. -/
theorem evb_trace_of_chain {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8} {k₁ sp₁ k₂ sp₂ : Nat}
    (h₁ : C₁ = openC₉ (openHeadC (walkSeed G S)) b)
    (hH₁ : H₁ = headPassC C₁ k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃ = closeCEnd (closeC₁₀b H₂) spz c8)
    (hb3 : (ifEnd24St b).toNat = 3)
    (hc8 : c8 = BitVec.ofNat 8 4)
    (hev : ev = EventRecord.number evbBits) :
    C₃.events = evbRecords := by
  have h1 : C₃.events =
      (((walkSeed G S).events ++ [EventRecord.tag (ifEnd24St b).toNat]) ++ [ev]) ++
        [EventRecord.tag c8.toNat] := by
    rw [h₃, hH₂, h₂, hH₁, h₁]
  rw [h1, hb3, hc8, hev]
  simp [evbRecords, walkSeed]

/-- **The carried event extent is the stream's width.**  `WalkInv.evlen_eq` names
the cursor as the staged one plus the trace's widths; at `[1]` the staged one is
zero and the trace's widths sum to the stream's eleven bytes. -/
theorem evb_evlen_of_trace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hnev0 : G.nev0 = 0) (hevents : C.events = evbRecords) :
    C.evlen = evbEvents.length := by
  have hsum : (evbRecords.map EventRecord.encodedSize).sum = 11 := by
    simp [evbRecords, EventRecord.encodedSize_tag, EventRecord.encodedSize_number]
  rw [hInv.evlen_eq, hevents, hnev0, hsum, evbEvents_length]

/-- **The event bytes at the accept finalisation.**  The invariant reads the
stream at the carried cursor; the two stores the finalisation makes are outside
the event buffer by the staging's separation, so the read survives them. -/
theorem evb_evBytes_at_accept {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hnev0 : G.nev0 = 0) (hevents : C.events = evbRecords) :
    readBytes (walkFinishMemAccept G s.mem C.alen C.evlen) G.ev C.evlen =
      some evbEvents := by
  have hlen : C.evlen = evbEvents.length := evb_evlen_of_trace hInv hnev0 hevents
  have hraw : readBytes s.mem G.ev (evbEvents.length) = some evbEvents := by
    simpa [hnev0, hevents, evbEvents] using hInv.evBytes
  have hshort : readBytes s.mem G.ev C.evlen = some evbEvents := by
    rw [hlen]; exact hraw
  have hevlen_le : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
  obtain ⟨-, -, houtN, houtV⟩ := stage2Regions_payload_outside G.separate
  rw [walkFinishMemAccept,
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

/-! ### The caller's result -/

/-- **The accepting return and the caller-visible reads at `[1]`, from the walk's
execution.**  The five counted segments compose the run to the merge; the accept
route's execution from that merge returns the verdict `1` at
`walkFinishMemAccept`, and the returned memory's four reads (the `JsonWalkReads`
interface) are rebuilt from the finalisation.  The arena cursor is zero, the
event stream is `evbEvents`, and the indexed reader's value is the reference
parser's canonical value.

Every hypothesis is stated above in the module docstring: the caller's staging
and the call's layout, the walk's execution, and the merge's own exit selection.
No verdict, no output byte, no cursor value and no parser fact is assumed. -/
theorem evb_caller_result {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {s₀ s₁ sh₁ s₂ sh₂ s₃ : State}
    {p₁ p₂ p₃ : Nat} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8} {k₁ sp₁ k₂ sp₂ : Nat}
    -- (1) the caller's staging and the call's layout
    (hpre : routePre evbLayout evbDoc)
    (hstageWord : readBytes m0 G.ndst 8 = readBytes evbMem evbLayout.ndst 8)
    (hndstG : G.ndst = evbLayout.ndst)
    (hnevG : G.nev = evbLayout.nev)
    (hdstG : G.dst = evbLayout.dst)
    (hevG : G.ev = evbLayout.ev)
    (hnev0 : G.nev0 = 0)
    -- (2) the execution: the five segments, their carries, the document's tag
    -- bytes and the numeral's record
    (hopen : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀ C₁ s₁ p₁)
    (hhead₁ : WalkSegment (stage2Calls stage2SubCalls) G C₁ s₁ H₁ sh₁ 2)
    (hnumber : WalkSegment (stage2Calls stage2SubCalls) G H₁ sh₁ C₂ s₂ p₂)
    (hhead₂ : WalkSegment (stage2Calls stage2SubCalls) G C₂ s₂ H₂ sh₂ 2)
    (hcloser : WalkSegment (stage2Calls stage2SubCalls) G H₂ sh₂ C₃ s₃ p₃)
    (h₁ : C₁ = openC₉ (openHeadC (walkSeed G S)) b)
    (hH₁ : H₁ = headPassC C₁ k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃ = closeCEnd (closeC₁₀b H₂) spz c8)
    (hb3 : (ifEnd24St b).toNat = 3)
    (hc8 : c8 = BitVec.ofNat 8 4)
    (hevRec : ev = EventRecord.number evbBits)
    -- (3) the merge's exit selection: the registers, the phis and the two tests
    {p : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hmergePre : s₃.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s₃ spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s₃ kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnp : lookupName s₃.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat)
    (hsp0 : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1)
    {rv : BitVec 32}
    (hrootRead : readBytes s₃.mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (hroot0 : evalICmp .eq rv (BitVec.ofNat 32 0) = 0) :
    ∃ (q : Nat) (m : Mem) (nev' : Nat),
      q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls)
          ((((p₁ + 2) + p₂) + 2) + p₃ + (q + 2)) stage2Body s₀ =
        some (.ret (some (.int 64 1)) m) ∧
      JsonWalkReads G C₃ m ∧
      readBytes m evbLayout.ndst 8 = some (wordBytes 8 0) ∧
      readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
      nev' = evbEvents.length ∧
      readBytes m evbLayout.dst 0 = some ([] : List UInt8) ∧
      readBytes m evbLayout.ev nev' = some evbEvents ∧
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evbEvents) (ByteString.literal ([] : List UInt8))).bind
        valueOfEvents = scalarCanonValueOfBytes evbDoc ∧
      Nonempty EvbCertificate := by
  -- the chain: the composed run to the merge, its invariant and its empty spans
  obtain ⟨hseg, hInv, hspans⟩ :=
    bracket_walk_chain hopen hhead₁ hnumber hhead₂ hcloser h₁ hH₁ h₂ hH₂ h₃
  -- the staging's zeroed cursor
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsep⟩ := hpre
  have hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0) := by
    rw [hstageWord]
    exact evb_stage_ndst hsep
  -- the arena cursor is the staged zero
  have halen0 : C₃.alen = 0 := by
    have h1 := WalkInv.alen_eq_ndst0_of_spans_nil hInv hspans
    have h2 := ndst0_eq_zero_of_staged_zero G hstaged
    omega
  -- the merge's block, from the closer's carry
  have hblk : C₃.block = "cleanup478.i" := by
    rw [h₃]
  -- the log's word, at the carried cursor (the bounds collapse to the zero)
  obtain ⟨a, hge, hle, hlog⟩ := hInv.log_alen
  have haEq : a = C₃.alen := by omega
  -- the accept route's execution: verdict 1 at the finalisation's memory
  obtain ⟨q, hq, hrun, -⟩ :=
    walkFinishPost_accept G C₃ s₃ hInv hblk hInv.regs hInv.ptrs
      (walkFinalEnv_of_regs hInv.regs) hge hle hlog hmergePre hsp hspv hk hkv
      hnp hterm hsp0 hrootRead hroot0
  have hrunA := hrun
  rw [haEq] at hrunA
  -- the composed run
  have hrunAll : runFuel (stage2Calls stage2SubCalls)
      ((((p₁ + 2) + p₂) + 2) + p₃ + (q + 2)) stage2Body s₀ =
        some (.ret (some (.int 64 1))
          (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen)) := by
    rw [hseg.run (q + 2), hrunA]
  -- the returned memory's four reads, the walk's interface
  have hreads : JsonWalkReads G C₃ (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen) :=
    jsonWalkReads_of_mem hInv rfl
  -- the arena's read at zero
  have hndstRead :
      readBytes (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen) evbLayout.ndst 8 =
        some (wordBytes 8 0) := by
    rw [← hndstG, ← halen0]
    exact hreads.ndst
  have hnevRead :
      readBytes (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen) evbLayout.nev 8 =
        some (wordBytes 8 C₃.evlen) := by
    rw [← hnevG]
    exact hreads.nev
  -- the arena buffer at the zero extent is empty
  obtain ⟨arena, harena⟩ := hreads.arena
  have harena0 :
      readBytes (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen) G.dst 0 =
        some arena := by
    rw [← halen0]; exact harena
  have harenaNil : arena = [] := by
    have hnil : readBytes (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen) G.dst 0 =
        some ([] : List UInt8) := rfl
    exact Option.some.inj (harena0.symm.trans hnil)
  -- the event stream at the carried cursor
  have hevents : C₃.events = evbRecords :=
    evb_trace_of_chain h₁ hH₁ h₂ hH₂ h₃ hb3 hc8 hevRec
  have hevlen : C₃.evlen = evbEvents.length :=
    evb_evlen_of_trace hInv hnev0 hevents
  have hevRead :
      readBytes (walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen) evbLayout.ev
        C₃.evlen = some evbEvents := by
    rw [← hevG]
    exact evb_evBytes_at_accept hInv hnev0 hevents
  -- the canonical value
  have hvalue :
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evbEvents)
          (ByteString.literal ([] : List UInt8))).bind valueOfEvents =
        scalarCanonValueOfBytes evbDoc := by
    have hagree := eventsOfBytesIndexedAgrees (bs := ByteString.literal evbDoc)
      (evs := ByteString.literal evbEvents) (arena := ByteString.literal ([] : List UInt8))
    have hdec : eventsOfBytesIndexed (ByteString.literal evbDoc)
        (ByteString.literal evbEvents) (ByteString.literal ([] : List UInt8)) =
        eventsOfBytes evbDoc evbEvents [] := by
      simpa only [EventsOfBytesIndexedAgrees, ByteString.toList_literal] using hagree
    rw [hdec]
    exact evb_sliceOne_value_closed
  -- the certificate
  have hcert : Nonempty EvbCertificate :=
    ⟨JsonPipelineIR.pipelineBody.name, rfl, "pipeline.o", rfl,
      JsonPipelineIR.stage2Sym, rfl, "stage2.o", rfl, nativeAdapterSymbol, rfl,
      "probes/json/route/shim.c", rfl, JsonPipelineIR.pipelineBody, rfl, evbArgs,
      rfl, by simp [evbArgs, routeArgs]⟩
  refine ⟨q, walkFinishMemAccept G s₃.mem C₃.alen C₃.evlen, C₃.evlen,
    hq, hrunAll, hreads, hndstRead, hnevRead, hevlen, ?_, hevRead, hvalue, hcert⟩
  rw [← hdstG, ← harenaNil]
  exact harena0

/-! ### Axiom footprint -/

/-- info: 'LeanLLVM.Refinement.WalkScope.evb_trace_of_chain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evb_trace_of_chain

/-- info: 'LeanLLVM.Refinement.WalkScope.evb_evlen_of_trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evb_evlen_of_trace

/-- info: 'LeanLLVM.Refinement.WalkScope.evb_evBytes_at_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_evBytes_at_accept

/-- info: 'LeanLLVM.Refinement.WalkScope.evb_caller_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_caller_result

end WalkScope
end LeanLLVM.Refinement
