/-
The emitter's residue at `[1]`: which buffer the caller's staging can and cannot
pin.

`JsonEventPremisesOne`/`JsonEventPremisesOneParse` close the decoder side at
`[1]`; the one open premise is `EvbEmission` — the arena is `[]` and the event
buffer holds the trace's encoding.  This module is the forward direction: it
reads the event-producing call's post at the caller's staged arguments and asks
what those two buffer facts follow from.

# The buffers, as the post states them

`pipelineUnitsPost` — the units record's buffer post; `Sigma_pipeline` is the
stronger semantic post and is used for the event half below — names both
buffers, and it names them *at the extents the adapter reports*: the arena
cursor slot and the event cursor slot are read by `pipelineOutputExtents`, and
the payload reads are `readBytes m dst ndstU = some out` and
`readBytes m ev nev' = some evs` with `ndstU`/`nev'` those slot values.  So both
buffers are reachable from the post — the adapter's reported extents are exactly
the post's extents.

What the post does **not** do is pin the contents:

* the arena clause is `∃ ndstU ndst' out, ndstU ≤ ndst' ∧
  pipelineOutputExtents args o ndstU nev' ∧ readBytes m dst ndstU = some out`.
  `ndstU` is the arena cursor's *value after the run*, and the post says nothing
  about it beyond `ndstU ≤ ndst'`; `out` is whatever the destination buffer holds
  at that extent.  `evb_arena_not_empty` proves the clause is satisfiable at the
  caller's own staging with `ndstU = 1` and `out = [0] ≠ []`: the returned
  memory differs from the staging only in the destination cursor slot (which the
  post's frame already lists as writable), so every other read-bearing clause is
  the staging's own read (the zero-extent clauses — `readLanes32 … 0`,
  `readBytes … xp 0`, `readBytes … ev 0` — are vacuous).  Hence `EvbEmission.arena_eq` — `arena = []` — is a fact
  about the *walk* (its arena cursor reaches zero on `[1]`), not a consequence of
  the post;
* the event clause is `readBytes m ev nev' = some evs` together with the
  spec post's `eventRel bs arena evs t.tokens`.  The extent is the same slot
  mechanism, but here the *content* is constrained: for `[1]`'s three tokens the
  relation's constructors force `evs` to the three records' encoding (each
  constructor is keyed on the token, the number payload is `strtodSpec` of the
  reader's deterministic decomposition of the span's lexeme, and
  `evbReader : reader evbLex = some evbDecimal` fixes it).  The event half of
  `EvbEmission` is therefore derived from the post (`evb_events_of_post`), and
  the arena half is not an inversion at all: the destination buffer's reported
  extent is the buffer this direction cannot pin.

# What this means for the release

`EvbEmission` cannot be supplied from the caller's staging and the units post
alone.  The missing piece is a fact about the walk's arena cursor at `[1]`
(`ndstU = 0`), which the units post does not publish because it binds no record
trace.  The event buffer is derived from the post (`evb_events_of_post`), so the
residue is exactly the destination buffer's extent, not the event stream.

The clause therefore lives at the one predicate that has the trace in scope:
`Stage2OutcomeEvidence` states the reported extent as the staged cursor plus
`arenaExtent` of the trace, and at `[1]` that accounting is zero — so the arena
the run reports is empty, and `evb_emission_of_evidence` is a theorem of the
slice rather than an assumption.  Its conclusion names the returned memory and
the adapter's header extents: the arena read at `ndstU`, the event read at
`nev'`, the indexed decoder applied to those two buffers returning the canonical
value, and `EvbCertificate`, which names the linked symbol, the object and the
adapter the statement concerns and the body at the ABI it trusts.

`pipelineUnitsPost` and `Sigma_pipeline` cannot carry the extent clause (neither
binds a trace), so a release that consumes only the units post still takes the
arena datum.  `evb_events_of_post` remains the post-side route to the event
bytes for a consumer that has the semantic post and no evidence.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonEventPremisesOneParse
import LeanLLVM.Refinement.JsonEventCursorInterface
import LeanLLVM.Refinement.JsonAsciiSkip

set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The caller's staging at `[1]`

`RouteCall.stage`'s shape at `n = 3`: capacities `epcap = 73`, `xpcap = 72`,
`dstcap = 67`, `evcap = 167`, at separated addresses above the 8 KiB POS8 table
and the stage-2 work space. -/

/-- The caller's layout at `evbDoc` (`RouteCall.stage` at `n = 3`). -/
def evbLayout : RouteLayout where
  base := 4096
  tab := 8192
  sc := 20480
  mkSlot := 20544
  entw := 20608
  ep := 20672
  nk := 21056
  xp := 21120
  nxp := 21504
  xcarry := 21568
  dst := 21632
  ndst := 21760
  ev := 21824
  nev := 22016
  err := 22080
  epcap := 73
  xpcap := 72
  dstcap := 67
  evcap := 167
  arm := 0
  nxp0 := 0
  ndst0 := 0
  nev0 := 0

/-- The twenty-word argument list the object is called at. -/
def evbArgs : List Value := routeArgs evbLayout evbDoc

/-- The memory the caller stages. -/
def evbMem : Mem := stagedMem evbLayout evbDoc

/-! ### The staging's own extents

The two cursor slots the adapter reports, and the destination buffer's contents,
read straight off `stagedMem`.  These are the caller's numbers, not the run's. -/

/-- The arena cursor slot as staged: the empty arena's extent. -/
theorem evb_stage_ndst (hsep : DisjointRegions (stagedExtents evbLayout evbDoc)) :
    readBytes evbMem evbLayout.ndst 8 = some (wordBytes 8 0) := by
  simpa [evbMem, stagedMem, evbLayout, wordBytes, natToBytes_length] using
    store_read_full (m := []) (mem_ndst evbLayout evbDoc) hsep

/-- The event cursor slot as staged: the empty stream's extent. -/
theorem evb_stage_nev (hsep : DisjointRegions (stagedExtents evbLayout evbDoc)) :
    readBytes evbMem evbLayout.nev 8 = some (wordBytes 8 0) := by
  simpa [evbMem, stagedMem, evbLayout, wordBytes, natToBytes_length] using
    store_read_full (m := []) (mem_nev evbLayout evbDoc) hsep

/-- The entry stream's count slot as staged. -/
theorem evb_stage_nk (hsep : DisjointRegions (stagedExtents evbLayout evbDoc)) :
    readBytes evbMem evbLayout.nk 8 = some (wordBytes 8 0) := by
  simpa [evbMem, stagedMem, evbLayout, wordBytes, natToBytes_length] using
    store_read_full (m := []) (mem_nk evbLayout evbDoc) hsep

/-- The escape list's count slot as staged. -/
theorem evb_stage_nxp (hsep : DisjointRegions (stagedExtents evbLayout evbDoc)) :
    readBytes evbMem evbLayout.nxp 8 = some (wordBytes 8 0) := by
  simpa [evbMem, stagedMem, evbLayout, wordBytes, natToBytes_length] using
    store_read_full (m := []) (mem_nxp evbLayout evbDoc) hsep

/-- The destination buffer at its staged capacity. -/
theorem evb_stage_dst_full (hsep : DisjointRegions (stagedExtents evbLayout evbDoc)) :
    readBytes evbMem evbLayout.dst evbLayout.dstcap =
      some (List.replicate evbLayout.dstcap 0) := by
  simpa [evbMem, stagedMem, evbLayout, List.length_replicate] using
    store_read_full (m := []) (mem_dst evbLayout evbDoc) hsep

/-- The destination buffer's first byte at the staging: the arena is zero-filled,
so a one-byte read is `[0]`. -/
theorem evb_stage_dst_one (hsep : DisjointRegions (stagedExtents evbLayout evbDoc)) :
    readBytes evbMem evbLayout.dst 1 = some [0] := by
  have hfull := evb_stage_dst_full hsep
  rw [show evbLayout.dstcap = 67 from rfl] at hfull
  obtain ⟨h1, -⟩ := readBytes_split evbMem evbLayout.dst 1 66 hfull
  have htake : (List.replicate 67 (0 : UInt8)).take 1 = [0] := by decide
  rw [h1, htake]

/-! ### The frame the units post names at these arguments

The thirteen caller regions, the stage-2 report scratch at zero, and the
allocation interval `(0, 0)`.  The destination cursor's eight bytes are one of
them, which is what lets a returned memory differ there and nowhere else. -/

/-- The units post's frame list at the slice's witnesses. -/
def evbFrame : List (Nat × Nat) :=
  ([(evbLayout.sc, 24), (evbLayout.mkSlot, 48), (evbLayout.entw, 8),
    (evbLayout.ep, 4 * (0 + 8)), (evbLayout.nk, 8),
    (evbLayout.xp, 4 * (0 + batchReserve)), (evbLayout.nxp, 8),
    (evbLayout.xcarry, 16), (evbLayout.dst, 3 + 64), (evbLayout.ndst, 8),
    (evbLayout.ev, 0), (evbLayout.nev, 8), (evbLayout.err, 8)] ++
    stage2ReportScratch 0 0 0 0 0 0 0 0) ++ [(0, 0 - 0)]

/-- The destination cursor's slot is inside the frame. -/
theorem evbFrame_mem_ndst : (evbLayout.ndst, 8) ∈ evbFrame := by
  simp only [evbFrame, List.mem_append]
  left; left
  simp

/-- **The post's frame at a memory that differs only in the destination
cursor.**  The cursor's eight bytes are a listed region, so a write there keeps
the frame: every address outside the listed regions is outside that write's
range too. -/
theorem evbFrame_write (bs : List UInt8) (hlen : bs.length = 8) :
    UnchangedOutside evbMem (writeBytes evbMem evbLayout.ndst bs) evbFrame := by
  intro a ha
  have hnot : ¬ (evbLayout.ndst ≤ a ∧ a < evbLayout.ndst + 8) :=
    ha (evbLayout.ndst, 8) evbFrame_mem_ndst
  rcases Nat.lt_or_ge a evbLayout.ndst with hlt | hge
  · exact readByte_writeBytes_outside evbMem bs (Or.inl hlt)
  · refine readByte_writeBytes_outside evbMem bs (Or.inr ?_)
    rw [hlen]
    omega

/-! ### The destination buffer's extent is not pinned

The post's arena clause is satisfiable at the caller's staging with a *nonempty*
arena, by running the cursor slot up one byte.  Every other clause is the
staging's own read (the returned memory differs only in a listed region), so the
countermodel is a full `pipelineUnitsPost` at these arguments. -/

/-- A word's bytes are taken whole at their own width. -/
theorem natToBytes_take (v w : Nat) : (natToBytes v w).take w = natToBytes v w := by
  rw [List.take_of_length_le (by simp [natToBytes_length])]

/-- **The arena is not `[]` by the units post alone.**  At the caller's staged
arguments for `[1]`, there is a returned memory whose destination cursor reads
`1` and whose destination buffer holds `[0]` at that extent, and which satisfies
`pipelineUnitsPost` at the accepted verdict.  The staging's own cursor reads `0`
(`evb_stage_ndst`), so both extents are consistent with the caller's staging:
which one is reported is the walk's fact, not the caller's or the post's. -/
theorem evb_arena_not_empty (hpre : routePre evbLayout evbDoc) :
    ∃ (m : Mem) (out : List UInt8),
      out ≠ [] ∧
      pipelineUnitsPost evbArgs evbMem (routeNext evbLayout evbDoc)
        (.ret (some (.int 64 1)) m) ∧
      readBytes m evbLayout.dst out.length = some out := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsep⟩ := hpre
  let m : Mem := writeBytes evbMem evbLayout.ndst (wordBytes 8 1)
  let out : List UInt8 := [0]
  have hmem : readBytes m evbLayout.ndst 8 = some (wordBytes 8 1) := by
    show readBytes (writeBytes evbMem evbLayout.ndst (wordBytes 8 1))
      evbLayout.ndst 8 = some (wordBytes 8 1)
    simpa [wordBytes, natToBytes_length, natToBytes_take] using
      readBytes_writeBytes_from evbMem (wordBytes 8 1) evbLayout.ndst 0 8
        (by simp [wordBytes, natToBytes_length])
  have hdst : readBytes m evbLayout.dst 1 = some out := by
    show readBytes (writeBytes evbMem evbLayout.ndst (wordBytes 8 1))
      evbLayout.dst 1 = some [0]
    rw [readBytes_writeBytes_outside evbMem (wordBytes 8 1)
      (Or.inr (by decide : evbLayout.dst + 1 ≤ evbLayout.ndst))]
    exact evb_stage_dst_one hsep
  have hnkm : readBytes m evbLayout.nk 8 = some (wordBytes 8 0) := by
    show readBytes (writeBytes evbMem evbLayout.ndst (wordBytes 8 1))
      evbLayout.nk 8 = some (wordBytes 8 0)
    rw [readBytes_writeBytes_outside evbMem (wordBytes 8 1)
      (Or.inr (by decide : evbLayout.nk + 8 ≤ evbLayout.ndst))]
    exact evb_stage_nk hsep
  have hnxpm : readBytes m evbLayout.nxp 8 = some (wordBytes 8 0) := by
    show readBytes (writeBytes evbMem evbLayout.ndst (wordBytes 8 1))
      evbLayout.nxp 8 = some (wordBytes 8 0)
    rw [readBytes_writeBytes_outside evbMem (wordBytes 8 1)
      (Or.inr (by decide : evbLayout.nxp + 8 ≤ evbLayout.ndst))]
    exact evb_stage_nxp hsep
  have hnevm : readBytes m evbLayout.nev 8 = some (wordBytes 8 0) := by
    show readBytes (writeBytes evbMem evbLayout.ndst (wordBytes 8 1))
      evbLayout.nev 8 = some (wordBytes 8 0)
    rw [readBytes_writeBytes_outside evbMem (wordBytes 8 1)
      (Or.inl (by decide : evbLayout.ndst + 8 ≤ evbLayout.nev))]
    exact evb_stage_nev hsep
  have herrm : readBytes m evbLayout.err 8 = readBytes evbMem evbLayout.err 8 := by
    show readBytes (writeBytes evbMem evbLayout.ndst (wordBytes 8 1))
      evbLayout.err 8 = readBytes evbMem evbLayout.err 8
    rw [readBytes_writeBytes_outside evbMem (wordBytes 8 1)
      (Or.inl (by decide : evbLayout.ndst + 8 ≤ evbLayout.err))]
  refine ⟨m, out, by decide, ?_, ?_⟩
  · unfold pipelineUnitsPost evbArgs routeArgs
    refine ⟨by decide, 0, 0, 1, 3, 0, [], [], out, [], 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, by decide, ?_, hnkm, hnxpm, rfl, rfl, hdst, rfl, ?_, ?_, by decide, ?_⟩
    · -- the output extents
      unfold pipelineOutputExtents
      exact ⟨by decide, by decide, hmem, hnevm⟩
    · -- the refusal branch is vacuous at the accepted verdict
      intro h
      exact absurd h (by decide)
    · -- the refusal slot is outside the cursor write
      intro _
      exact herrm
    · -- the frame
      exact evbFrame_write (wordBytes 8 1) (by simp [wordBytes, natToBytes_length])
  · show readBytes m evbLayout.dst 1 = some [0]
    exact hdst

/-! ### What this rules out, and what it leaves

`EvbEmission.arena_eq` would need `out = []` from the post.  The theorem above
exhibits a post-satisfying returned memory with `out = [0]`, so no such
derivation exists at this staging: the destination buffer's reported extent is
the buffer the forward direction cannot pin.  The event buffer's *content* is
derived below (`evb_events_of_post`): the spec post's `eventRel` at `[1]`'s three
tokens forces the three records' encoding.  So the residue is the arena alone. -/

/-- info: 'LeanLLVM.Refinement.evb_stage_dst_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_stage_dst_one

/-- info: 'LeanLLVM.Refinement.evbFrame_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evbFrame_write

/-- info: 'LeanLLVM.Refinement.evb_arena_not_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_arena_not_empty


/-! ### The event half: `[1]`'s three tokens force the three records

`Stage2EventRel`'s constructors are keyed on the token head, so a token list of
three known tokens forces the byte stream's shape record by record.  The
inversions are the `Stage2EventRel` counterparts of
`JsonEventBridgeEventsB`'s `inv_*` lemmas (which are stated for `Stage2Records`),
and `cases h` closes every constructor whose token head differs, exactly as
there. -/

/-- The empty token list forces the empty stream. -/
theorem evbInv_nil {bs arena : List UInt8} {evs : List UInt8}
    (h : Stage2EventRel bs arena evs []) : evs = [] := by
  cases h with
  | nil => rfl

/-- An `[` head forces the `T_ARR` tag record. -/
theorem evbInv_openBracket {bs arena : List UInt8} {evs : List UInt8} {s : Span}
    {toks : List Token} (h : Stage2EventRel bs arena evs (.punct .openBracket s :: toks)) :
    ∃ evs0, evs = tagRecord 3 ++ evs0 ∧ Stage2EventRel bs arena evs0 toks ∧
      bs[s.start]? = some 0x5B ∧ s.stop = s.start + 1 := by
  cases h with
  | openBracket hb hs h' => exact ⟨_, rfl, h', hb, hs⟩

/-- A `]` head forces the `T_ARR_END` tag record. -/
theorem evbInv_closeBracket {bs arena : List UInt8} {evs : List UInt8} {s : Span}
    {toks : List Token} (h : Stage2EventRel bs arena evs (.punct .closeBracket s :: toks)) :
    ∃ evs0, evs = tagRecord 4 ++ evs0 ∧ Stage2EventRel bs arena evs0 toks := by
  cases h with
  | closeBracket hb hs h' => exact ⟨_, rfl, h'⟩

/-- A number head forces the `T_NUM` record and the reader's decomposition. -/
theorem evbInv_number {bs arena : List UInt8} {evs : List UInt8} {s : Span}
    {toks : List Token} (h : Stage2EventRel bs arena evs (.number s :: toks)) :
    ∃ (evs0 : List UInt8) (d : Decimal) (lex : Bytes),
      evs = numberRecordBytes (strtodSpec d).toBits ++ evs0 ∧
      StrtodReader.reader lex = some d ∧
      s.stop = s.start + lex.length ∧
      (bs.drop s.start).take (s.stop - s.start) = lex.data.toList ∧
      Stage2EventRel bs arena evs0 toks := by
  cases h with
  | number hread hs hlex h' => exact ⟨_, _, _, rfl, hread, hs, hlex, h'⟩

/-- The trace's byte stream written as the three records. -/
theorem evbEvents_form :
    evbEvents = tagRecord 3 ++ numberRecordBytes evbBits ++ tagRecord 4 := by
  simp [evbEvents, evbRecords, tagRecord, numberRecordBytes, EventRecord.encodedBytes,
    numberRecord, stage2TagNum, List.flatten_cons, List.flatten_nil]

/-- **The arena is free at the relation.**  For `[1]` the three records satisfy
`Stage2EventRel` at *every* arena: none of the three constructors reads a body,
so their side conditions are arena-free.  With `evb_events_of_rel` this fixes the
stream and leaves the arena parameter unconstrained. -/
theorem evb_rel_arena_free (arena : List UInt8) :
    Stage2EventRel evbDoc arena evbEvents evbTokens := by
  rw [evbEvents_form]
  refine Stage2EventRel.openBracket (s := ⟨0, 1⟩) (by decide) (by decide) ?_
  refine Stage2EventRel.number (s := ⟨1, 2⟩) (d := evbDecimal) (lex := evbLex) ?_ ?_ ?_ ?_
  · exact evbReader
  · simp [evbLex]
  · simp [evbDoc, evbLex, ByteString.data_toList_literal]
  · exact Stage2EventRel.closeBracket (s := ⟨2, 3⟩) (by decide) (by decide)
      Stage2EventRel.nil

/-- **The event stream at `[1]`'s tokens is the three-record encoding.**  The
three inversions consume the opener, the number and the closer; the closer's
tail is empty, the number's lexeme is the span's one byte (`0x31`, so the reader
returns `evbDecimal` by determinism), and the payload is therefore `evbBits`. -/
theorem evb_events_of_rel {arena evs : List UInt8}
    (h : Stage2EventRel evbDoc arena evs evbTokens) : evs = evbEvents := by
  obtain ⟨e1, rfl, h1, -, -⟩ := evbInv_openBracket h
  obtain ⟨e2, d, lex, rfl, hread, hspan, hlexeme, h2⟩ := evbInv_number h1
  obtain ⟨e3, rfl, h3⟩ := evbInv_closeBracket h2
  have he3 : e3 = [] := evbInv_nil h3
  subst he3
  -- the span's lexeme is `0x31`, so `lex` is `evbLex` and `d` is `evbDecimal`
  have hdl : lex.data.toList = [0x31] := by
    rw [← hlexeme]
    decide
  have hlex : lex = evbLex := by
    rw [← ByteString.literal_toList lex]
    show ByteString.literal lex.toList = ByteString.literal [0x31]
    rw [ByteString.toList_eq_data_toList, hdl]
  subst hlex
  have hd : d = evbDecimal := by
    have h' : some evbDecimal = some d := evbReader.symm.trans hread
    exact (Option.some.inj h').symm
  subst hd
  rw [evbEvents_form]
  rfl


/-! ### The event half from the specification post

`Sigma_pipeline`'s accepting branch reads the event buffer at the cursor slot
(`nev`) and relates the bytes by `stage2EventRel`.  At the caller's staging the
document is `evbDoc` (`stagedDoc_read`), the parser's tape is `evbTape`
(`evb_parse` and `Except.ok` injectivity), and the relation is
`Stage2EventRel evbDoc arena evs evbTokens`; `evb_events_of_rel` then fixes the
bytes. -/

/-- **The event buffer's content, from the specification post.**  Every event
stream the accepted post leaves at the `nev` slot is `evbEvents`.  The arena
parameter stays free — that is the residue `evb_arena_not_empty` isolates. -/
theorem evb_events_of_post {m : Mem} {next : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hpost : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m)) :
    ∃ (nev' : Nat) (evs : List UInt8),
      readBytes m evbLayout.ev nev' = some evs ∧ evs = evbEvents := by
  obtain ⟨_, hb3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsep⟩ := hpre
  simp only [Sigma_pipeline, evbArgs, routeArgs] at hpost
  obtain ⟨bs, nk', nxp', ndstU, ndst', nev', hlen, hread, -, -, -, -, -, -, -,
    hacc, -, -⟩ := hpost
  have hn : (BitVec.ofNat 64 evbDoc.length).toNat = evbDoc.length :=
    bitVecOfNat_toNat (by decide)
  rw [hn] at hread
  have hbs : bs = evbDoc :=
    Option.some.inj (hread.symm.trans (stagedDoc_read evbLayout evbDoc hsep hb3))
  obtain ⟨t, v, arena, evs, hparse, -, -, hdst, hev, hrel, -, -⟩ := hacc trivial
  rw [hbs] at hparse
  have ht : t = evbTape := ParseResult.ok.inj (hparse.symm.trans evb_parse)
  have hrel' : Stage2EventRel evbDoc arena evs evbTokens := by
    have h' := hrel
    simp only [stage2EventRel] at h'
    rw [hbs, ht] at h'
    exact h'
  exact ⟨nev', evs, hev, evb_events_of_rel hrel'⟩

/-! ### The arena at `[1]`, from the evidence

`arenaExtent` counts the escaped bodies the trace names, and `[1]`'s trace is
three bodyless records: the opener's and the closer's tags and the number's
payload.  So the accounting is zero, the evidence's extent equation reduces to
the staged cursor, and the caller's staged cursor is zero.  The destination's
reported prefix is therefore empty — the fact `EvbEmission.arena_eq` had to
assume is a consequence of the evidence, not a further datum.

The trace is `evbRecords` and not merely *some* three-record list: each
`Stage2Records` constructor fixes its record's class and payload, the closer's
tail is empty, and the number's lexeme is the span's one byte, so the reader's
decimal is `evbDecimal` by determinism. -/

/-- **`[1]`'s trace is `evbRecords`.**  The three constructors are consumed in
order; the number's span is `1..2`, whose one byte is `0x31`, so the reader's
decomposition is `evbDecimal` and the payload is `evbBits`. -/
theorem evb_records_of_rel {arena : List UInt8} {rs : List EventRecord}
    (h : Stage2Records evbDoc arena rs evbTokens) : rs = evbRecords := by
  have htok : evbTokens = ([.punct .openBracket ⟨0, 1⟩, .number ⟨1, 2⟩,
      .punct .closeBracket ⟨2, 3⟩] : List Token) := rfl
  rw [htok] at h
  obtain ⟨rs1, rfl, h1⟩ := inv_openBracket h
  obtain ⟨rs2, d, lex, rfl, hread, -, hlex, h2⟩ := inv_number h1
  obtain ⟨rs3, rfl, h3⟩ := inv_closeBracket h2
  cases h3 with
  | nil =>
      have hdl : lex.data.toList = [0x31] := by
        rw [← hlex]
        decide
      have hlexe : lex = evbLex := by
        rw [← ByteString.literal_toList lex]
        show ByteString.literal lex.toList = ByteString.literal [0x31]
        rw [ByteString.toList_eq_data_toList, hdl]
      subst hlexe
      have hd : d = evbDecimal := by
        have h' : some evbDecimal = some d := evbReader.symm.trans hread
        exact (Option.some.inj h').symm
      subst hd
      rfl

/-- **`[1]`'s trace accounts for no arena bytes.**  Three records, none in the
escaped form. -/
theorem evb_arenaExtent_nil : arenaExtent evbRecords = 0 := rfl

/-- **The evidence pins `[1]`'s arena extent to zero.**  The trace's accounting
is `0`, the staged cursor reads `0` in the caller's staging, and the recorded
pair bounds the extent below `2 ^ 64`, so the extent equation forces `ndst' = 0`
and every destination read at or below it is empty. -/
theorem evb_arena_extent_zero_of_evidence {m : Mem} {ndst' nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndst' nev')
    (h : Stage2OutcomeEvidence evbLayout.base evbArgs evbMem ndst' nev'
      (.ret (some (.int 64 1)) m)) :
    ∃ (arena : List UInt8),
      ndst' = 0 ∧ readBytes m evbLayout.dst ndst' = some arena ∧ arena = [] ∧
      (∀ (n : Nat) (a : List UInt8),
        n ≤ ndst' → readBytes m evbLayout.dst n = some a → a = []) := by
  obtain ⟨_, hb3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsep⟩ := hpre
  simp only [pipelineOutputExtents, evbArgs, routeArgs] at hext
  obtain ⟨hextLt, -, -, -⟩ := hext
  simp only [Stage2OutcomeEvidence, evbArgs, routeArgs] at h
  obtain ⟨bs, _, hread, hcase⟩ := h
  rcases hcase with
    ⟨-, -, t, rs, arena, evs, hparse, hdst, hev, hrecs, hrel,
      ndst0, hndst0read, hndst0eq⟩ |
    ⟨hv0, -, -⟩
  · have hn : (BitVec.ofNat 64 evbDoc.length).toNat = evbDoc.length :=
      bitVecOfNat_toNat (by decide)
    rw [hn] at hread
    have hbs : bs = evbDoc :=
      Option.some.inj (hread.symm.trans (stagedDoc_read evbLayout evbDoc hsep hb3))
    rw [hbs] at hparse
    have ht : t = evbTape := ParseResult.ok.inj (hparse.symm.trans evb_parse)
    have hrel' : Stage2Records evbDoc arena rs evbTokens := by
      rw [hbs, ht] at hrel
      exact hrel
    have hrs : rs = evbRecords := evb_records_of_rel hrel'
    have hzero : arenaExtent rs = 0 := by rw [hrs]; rfl
    have hndst' : ndst' = ndst0 := by rw [hndst0eq, hzero, Nat.add_zero]
    have hstage : readBytes evbMem evbLayout.ndst 8 = some (wordBytes 8 0) :=
      evb_stage_ndst hsep
    have hword : wordBytes 8 ndst0 = wordBytes 8 0 :=
      Option.some.inj (hndst0read.symm.trans hstage)
    have hres : ndst0 % 2 ^ 64 = 0 := by simpa using wordBytes_residue hword
    have hndst0Lt : ndst0 < 2 ^ 64 := by omega
    have hndst0 : ndst0 = 0 := by
      have h := Nat.mod_eq_of_lt hndst0Lt
      omega
    have hz : ndst' = 0 := by omega
    subst hz
    have hnil : readBytes m evbLayout.dst 0 = some ([] : List UInt8) := rfl
    refine ⟨arena, rfl, hdst, ?_, ?_⟩
    · exact (Option.some.inj (hnil.symm.trans hdst)).symm
    · intro n a hn hread'
      have hn0 : n = 0 := by omega
      subst hn0
      exact (Option.some.inj (hnil.symm.trans hread')).symm
  · exact absurd hv0 (by decide)

/-- **The event buffer's content and extent, from the evidence.**  The evidence
reads the event buffer at the value of the adapter's `nev` slot, and `[1]`'s
trace is `evbRecords`, so the bytes it read are `evbEvents`.  This is the
evidence-side counterpart of `evb_events_of_post`: the post fixes the same
bytes, while the evidence additionally names the extent the adapter reported. -/
theorem evb_events_of_evidence {m : Mem} {ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hev : Stage2OutcomeEvidence evbLayout.base evbArgs evbMem ndstU nev'
      (.ret (some (.int 64 1)) m)) :
    ∃ evs : List UInt8,
      readBytes m evbLayout.ev nev' = some evs ∧ evs = evbEvents := by
  obtain ⟨_, hb3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsep⟩ := hpre
  simp only [Stage2OutcomeEvidence, evbArgs, routeArgs] at hev
  obtain ⟨bs, _, hread, hcase⟩ := hev
  rcases hcase with
    ⟨-, -, t, rs, arena, evs, hparse, -, hreadEv, hrecs, hrel, -, -, -⟩ |
    ⟨hv0, -, -⟩
  · have hn : (BitVec.ofNat 64 evbDoc.length).toNat = evbDoc.length :=
      bitVecOfNat_toNat (by decide)
    rw [hn] at hread
    have hbs : bs = evbDoc :=
      Option.some.inj (hread.symm.trans (stagedDoc_read evbLayout evbDoc hsep hb3))
    rw [hbs] at hparse
    have ht : t = evbTape := ParseResult.ok.inj (hparse.symm.trans evb_parse)
    have hrel' : Stage2Records evbDoc arena rs evbTokens := by
      rw [hbs, ht] at hrel
      exact hrel
    have hrs : rs = evbRecords := evb_records_of_rel hrel'
    refine ⟨evs, hreadEv, ?_⟩
    rw [hrecs, hrs]
    exact evb_events.symm
  · exact absurd hv0 (by decide)

/-- **The linked unit a release certificate for the event route names, and the
transfer it trusts.**

`linkedSymbol` is the exported name of the object the adapter calls, `linkedObject`
that object, `emitterSymbol` and `emitterObject` the stage-2 unit that writes the
event buffer, and `adapter` the `@[extern]` the Lean caller reaches.
`adapterSource` names the C file behind that symbol.  `body` and `staging` are
the transfer: the linked body is the pinned `pipelineBody`, called with the
twenty argument values `evbArgs` stages.  That clang preserves that body and that
the link reaches it are `docs/contract.md` rows 8 and 9 — the compiler/FFI trust
boundary `JsonCallRoute.missingBridgePieces` records — stated here so the
certificate discloses it rather than leaving it implicit.

The header extents themselves are in `evb_emission_of_evidence`'s conclusion;
the certificate is about the linked unit, not about one run's buffers. -/
structure EvbCertificate : Type where
  /-- The linked object's exported symbol (`pipeline.h`). -/
  linkedSymbol : String
  linkedSymbol_eq : linkedSymbol = JsonPipelineIR.pipelineBody.name
  /-- The object `probes/json/route/build.sh` links as `pipeline.o`. -/
  linkedObject : String
  linkedObject_eq : linkedObject = "pipeline.o"
  /-- The stage-2 unit's symbol, which writes the event buffer. -/
  emitterSymbol : String
  emitterSymbol_eq : emitterSymbol = JsonPipelineIR.stage2Sym
  /-- The stage-2 object `build.sh` links as `stage2.o`. -/
  emitterObject : String
  emitterObject_eq : emitterObject = "stage2.o"
  /-- The adapter the Lean caller's `@[extern]` reaches. -/
  adapter : String
  adapter_eq : adapter = nativeAdapterSymbol
  /-- The adapter's source, outside `lake`. -/
  adapterSource : String
  adapterSource_eq : adapterSource = "probes/json/route/shim.c"
  /-- The body the linked object is trusted to implement. -/
  body : Function
  body_eq : body = JsonPipelineIR.pipelineBody
  /-- The ABI values the adapter stages. -/
  staging : List Value
  staging_eq : staging = evbArgs
  /-- Twenty values: `routeArgs`'s list. -/
  staging_arity : staging.length = 20

/-- **The emission at `[1]`, at the buffers the run returned.**  Both payload
reads name the same returned memory `m` and the lengths the adapter's header
carries — `ndstU` from the `ndst` slot and `nev'` from the `nev` slot.  The
indexed decoder applied to exactly those two reads returns the reference's
canonical value, and the certificate names the linked symbol, the object, the
adapter and the body/ABI transfer the statement trusts.

The arena extent is zero from the evidence (`evb_arena_extent_zero_of_evidence`);
the event bytes are the evidence's read at the header's `nev'`
(`evb_events_of_evidence`) and are the trace's encoding.  The specification post
is no longer a hypothesis: the evidence carries both buffers at the reported
extents, so `evb_events_of_post` stays as the post-side route for a consumer that
does not have the evidence. -/
theorem evb_emission_of_evidence {m : Mem} {ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hev : Stage2OutcomeEvidence evbLayout.base evbArgs evbMem ndstU nev'
      (.ret (some (.int 64 1)) m)) :
    ∃ (arena evs : List UInt8),
      readBytes m evbLayout.ndst 8 = some (wordBytes 8 ndstU) ∧
      readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
      readBytes m evbLayout.dst ndstU = some arena ∧
      readBytes m evbLayout.ev nev' = some evs ∧
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evs) (ByteString.literal arena)).bind valueOfEvents =
        scalarCanonValueOfBytes evbDoc ∧
      Nonempty EvbCertificate := by
  obtain ⟨arena, -, hreadA, hnil, -⟩ :=
    evb_arena_extent_zero_of_evidence hpre hext hev
  obtain ⟨evs, hreadE, hevEq⟩ := evb_events_of_evidence hpre hev
  simp only [pipelineOutputExtents, evbArgs, routeArgs] at hext
  obtain ⟨-, -, hdrNdst, hdrNev⟩ := hext
  refine ⟨arena, evs, hdrNdst, hdrNev, hreadA, hreadE, ?_, ?_⟩
  · have hagree := eventsOfBytesIndexedAgrees (bs := ByteString.literal evbDoc)
      (evs := ByteString.literal evs) (arena := ByteString.literal arena)
    have hdec : eventsOfBytesIndexed (ByteString.literal evbDoc)
        (ByteString.literal evs) (ByteString.literal arena) =
        eventsOfBytes evbDoc evs arena := by
      simpa only [EventsOfBytesIndexedAgrees, ByteString.toList_literal] using hagree
    rw [hdec, hevEq, hnil]
    exact evb_sliceOne_value evb_parse
  · exact ⟨JsonPipelineIR.pipelineBody.name, rfl, "pipeline.o", rfl,
      JsonPipelineIR.stage2Sym, rfl, "stage2.o", rfl, nativeAdapterSymbol, rfl,
      "probes/json/route/shim.c", rfl, JsonPipelineIR.pipelineBody, rfl, evbArgs,
      rfl, by simp [evbArgs, routeArgs]⟩

/-! ### The finding, and the repair

The arena's content at its reported extent is **not determined by the units
postcondition**: `evb_arena_not_empty` exhibits a returned memory that satisfies
every conjunct of `pipelineUnitsPost` at the accepted verdict with `ndst = 1` and
`[0]` in the destination buffer at that extent, while the caller's own cursor
slot reads `0` (`evb_stage_ndst`).  The event buffer is the opposite case:
`evb_events_of_post` derives `evs = evbEvents` from the specification post.

So the clause has to be added where a trace is in scope, and that is the outcome
evidence:

* `Stage2OutcomeEvidence` (`JsonStage2Hsem.lean`) now reads the staged arena
  cursor off the starting memory and states `ndst' = ndst0 + arenaExtent rs`.
  `arenaExtent` counts one `len` per record in the escaped form (`strArena`,
  whose field is an arena offset); the plain form's body lives in the document
  and appends nothing.  The *bytes* of each escaped body are not a function of
  the trace — they are the decoder's output, which the record names by extent and
  offset — so the accounting, not a reconstructed buffer, is what the trace can
  state;
* `pipelineUnitsPost` cannot carry the clause: it binds no trace.  Neither can
  `Sigma_pipeline`'s acceptance tuple, for the same reason — it binds the byte
  relation and not `rs` — so the clause lives at the evidence, which both the
  specification and the units record are released against
  (`pipeline_satisfies_stage2_of_evidence`);
* at `[1]` the trace is `evbRecords` (`evb_records_of_rel`), its accounting is
  `0` (`evb_arenaExtent_nil`), and the staged cursor is `0` (`evb_stage_ndst`), so
  the recorded extent is `0` (`evb_arena_extent_zero_of_evidence`) and every
  destination read at or below it is `[]`.  `evb_emission_of_evidence` then
  states the emission at the returned memory: both payload reads at the header's
  extents, the indexed decoder on those two buffers returning the canonical
  value, and `EvbCertificate` naming the linked symbol, object, adapter and the
  body/ABI transfer.  `evb_events_of_evidence` is the evidence-side event read;
  `evb_events_of_post` remains the same content from the specification post.

The arena is free *at the relation* too (`evb_rel_arena_free`: every arena
satisfies `Stage2EventRel` at `[1]`'s records, because none of the three
constructors reads a body), so the relation itself cannot constrain it; the
arena's content is a *walk* fact (the cursor reaches zero on `[1]`), not a
consequence of anything the caller stages, the relation states, or the units post
states; `evb_arena_not_empty` is the evidence for that sentence and is not
weakened.  A release theorem that consumes only the units post still takes the
arena datum, because the units post still binds no trace.
-/

/-! ### The terminating run from the staged entry

`evb_emission_of_evidence` concludes the emission from the outcome evidence
`hev`.  This section states the run that supplies it and proves every conjunct
the staged entry determines on its own.

**The fuel and the staging.**  `pipelineBudget` reads the document's block count
off the ABI's third argument, and `[1]` is one block: `pipelineBudget evbArgs
evbMem = 20` (`evb_budget`).  `routePre` establishes the body's staging
(`evb_staging`), which is the record's precondition through `routeSpecPre`.

**The run.**  `Γ_pipeline_units` is the record the pinned body satisfies: its
completion conjunct names a returning run at the record's own fuel from
`EntryState JsonPipelineIR.pipelineBody evbArgs evbMem (routeNext evbLayout evbDoc)`, and its
post is forced at that outcome.  `evb_run_terminates` is that instantiation; the
post pins the return to the ABI's verdict word (`routePost_result` reads the two
values off it).

**The evidence at the run's accepted outcome.**  Beyond the specification post,
the evidence at `[1]` carries two walk facts: the record trace related to the
tape's tokens, and the reported arena extent being the staged cursor plus the
trace's accounting.  The first is *not* a fact about the run at this document —
`[1]`'s trace is `evbRecords`, and its relation to `evbTape`'s tokens is
`evb_records`, read off the document's spelling — and the second's accounting is
zero (`evb_arenaExtent_nil`).  So the only fact left is that the cursor the run
reports is the staged one, zero here.  `evb_evidence_of_spec` assembles the
evidence from the specification post at the accepting verdict and that cursor
fact; `evb_emission_of_spec` is `evb_emission_of_evidence` at it, and
`evb_run_to_emission` states the pair at the run that produces it.

**The boundary.**  The specification post at the accepting outcome is the stage-2
call's own: the parser's tape, the event stream's relation to its tokens and the
two buffer reads.  Its producer is the walk's accepted arm, and on the number's
route that arm still needs the numeral's read-back — the record `num_fast_el1`'s
output slot holds, `f.ev = EventRecord.number (strtodSpec d).toBits`, which
`JsonStage2WalkRowArms.numberArmSegment` takes and does not prove.  The
conversion's run is not in the tree: `JsonStage2NumFastCalleeD8` models the
callees' bodies and the arm's segment and record are produced, but the three
digit runs, the inlined tier-1 arithmetic and the tier-2 kernel's exactness bound
are the open region.  The statements below therefore stop there: the terminating
run at the record's fuel, and the evidence from the run's accepting outcome given
that call's post. -/

/-- `[1]` is one 64-byte block. -/
theorem evb_blocks : pipelineBlocks evbDoc.length = 1 := by
  unfold pipelineBlocks evbDoc
  decide

/-- **The run's fuel at `[1]`**: one block and the tail's allowance. -/
theorem evb_budget : pipelineBudget evbArgs evbMem = 20 := by
  unfold pipelineBudget evbArgs routeArgs evbLayout evbDoc
    pipelineBlockAllowance pipelineFinalisationAllowance
  decide

/-- **The staging, from the route's precondition.** -/
theorem evb_staging (hpre : routePre evbLayout evbDoc) :
    pipelineStaging evbLayout.tab evbLayout.base evbArgs evbMem :=
  routeStaging evbLayout evbDoc hpre

/-- The event stream's width, from the records': two tag bytes and the number
record's nine. -/
theorem evbEvents_length : evbEvents.length = 11 := by
  simp [evbEvents, evbRecords, EventRecord.encodedBytes, numberRecord, wordBytes,
    List.flatten_cons, List.flatten_nil, natToBytes_length]

/-- The event stream's extent is inside the cursor word's width. -/
theorem evbEvents_length_lt : evbEvents.length < 2 ^ 64 := by
  rw [evbEvents_length]
  decide

/-- **The terminating run from the staged entry.**  At the route's arguments and
cursor the record's precondition holds (`routeSpecPre`), so the body has a
returning run at the record's own fuel and the record's post at that outcome.
The return carries a value — a void return and `.ub` are outside the post — and
that value is the ABI's verdict word. -/
theorem evb_run_terminates {calls : Calls}
    (hunits : Satisfies calls JsonPipelineIR.pipelineBody
      (Γ_pipeline_units evbLayout.tab evbLayout.base))
    (hpre : routePre evbLayout evbDoc) :
    ∃ (v : Value) (m : Mem),
      runFuel calls (pipelineBudget evbArgs evbMem) JsonPipelineIR.pipelineBody
        (EntryState JsonPipelineIR.pipelineBody evbArgs evbMem (routeNext evbLayout evbDoc)) =
        some (.ret (some v) m) ∧
      pipelineUnitsPost evbArgs evbMem (routeNext evbLayout evbDoc)
        (.ret (some v) m) := by
  obtain ⟨hst, hbelow, hwork, -⟩ := routeSpecPre evbLayout evbDoc hpre
  obtain ⟨hcom, hpostAll⟩ := hunits evbArgs evbMem (routeNext evbLayout evbDoc)
    ⟨hst, hbelow, hwork⟩
  obtain ⟨v₀, m, hrun⟩ := hcom
  cases v₀ with
  | none =>
      have hbad : pipelineUnitsPost evbArgs evbMem (routeNext evbLayout evbDoc)
          (.ret none m) := hpostAll (.ret none m) (Or.inr ⟨_, hrun⟩)
      exact absurd hbad (by
        intro h
        unfold pipelineUnitsPost at h
        exact h)
  | some v =>
      exact ⟨v, m, hrun, hpostAll (.ret (some v) m) (Or.inr ⟨_, hrun⟩)⟩

/-- **The evidence from the run's accepting outcome.**  The specification post at
the accepting verdict names the parser's tape, the event stream and the two
buffer reads; at `[1]` the trace is `evbRecords` and the arena accounting is
zero, so the only run fact the post does not carry is that the reported arena
cursor is the staged one — zero at this staging.  With it the evidence holds at
the reported extents. -/
theorem evb_evidence_of_spec {m : Mem} {next ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hspec : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m))
    (hndst : readBytes m evbLayout.ndst 8 = some (wordBytes 8 0)) :
    Stage2OutcomeEvidence evbLayout.base evbArgs evbMem ndstU nev'
      (.ret (some (.int 64 1)) m) := by
  obtain ⟨-, hb3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsep⟩ := hpre
  -- the header extents, and their bound on the cursor word
  simp only [pipelineOutputExtents, evbArgs, routeArgs] at hext
  obtain ⟨hndstLt, hnevLt, hndstSlot, hnevSlot⟩ := hext
  have hndstU : ndstU = 0 :=
    slotExtent_eq (x := ndstU) (y := 0) hndstLt (Nat.two_pow_pos 64) hndstSlot hndst
  -- the specification post at the accepting verdict
  simp only [Sigma_pipeline, evbArgs, routeArgs] at hspec
  obtain ⟨bs, nk', nxp', ndstUs, ndsts, nevs, hlen, hread, -, -, -, -,
    hnevSlotS, -, -, haccepted, -, -⟩ := hspec
  have hn : (BitVec.ofNat 64 evbDoc.length).toNat = evbDoc.length :=
    bitVecOfNat_toNat (by decide)
  rw [hn] at hread
  have hbs : bs = evbDoc :=
    Option.some.inj (hread.symm.trans (stagedDoc_read evbLayout evbDoc hsep hb3))
  obtain ⟨t, v, arena, evs, hparse, -, -, -, hevS, hrel, -, -⟩ :=
    haccepted trivial
  rw [hbs] at hparse
  have ht : t = evbTape := ParseResult.ok.inj (hparse.symm.trans evb_parse)
  have hrel' : Stage2EventRel evbDoc arena evs evbTokens := by
    have h' := hrel
    simp only [stage2EventRel] at h'
    rw [hbs, ht] at h'
    exact h'
  have hevs : evs = evbEvents := evb_events_of_rel hrel'
  -- the specification's event extent is the header's: both are the slot's word
  have hevsLen : evs.length = nevs :=
    JsonEntrySteps.readBytes_length m evbLayout.ev nevs hevS
  have hnevs : nevs = evbEvents.length := by rw [← hevsLen, hevs]
  have hnevsLt : nevs < 2 ^ 64 := by
    rw [hnevs]
    exact evbEvents_length_lt
  have hnevEq : nevs = nev' :=
    slotExtent_eq (x := nevs) (y := nev') hnevsLt hnevLt hnevSlotS hnevSlot
  have hev : readBytes m evbLayout.ev nev' = some evs := by
    rw [← hnevEq]
    exact hevS
  simp only [Stage2OutcomeEvidence, evbArgs, routeArgs]
  refine ⟨evbDoc, hn, ?_, Or.inl ⟨trivial, ?_, evbTape, evbRecords, [], evs,
    evb_parse, ?_, hev, ?_, evb_records, 0, evb_stage_ndst hsep, ?_⟩⟩
  · rw [hn]
    exact stagedDoc_read evbLayout evbDoc hsep hb3
  · rw [show pipelineBlocks evbDoc.length = JsonScanSpec.blocksOf evbDoc.length
        from rfl]
    exact skip_sound evbDoc (by decide : ∀ x ∈ evbDoc, x.toNat < 0x80)
  · rw [hndstU]
    rfl
  · exact hevs.trans evb_events
  · rw [hndstU]
    simp [evb_arenaExtent_nil]

/-- **The emission from the specification post and the reported cursor.**  This
is `evb_emission_of_evidence` at `evb_evidence_of_spec`: the emission theorem
with no outcome evidence as a premise, only the call's post at the accepting
verdict and the cursor the run reports. -/
theorem evb_emission_of_spec {m : Mem} {next ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hspec : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m))
    (hndst : readBytes m evbLayout.ndst 8 = some (wordBytes 8 0)) :
    ∃ (arena evs : List UInt8),
      readBytes m evbLayout.ndst 8 = some (wordBytes 8 ndstU) ∧
      readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
      readBytes m evbLayout.dst ndstU = some arena ∧
      readBytes m evbLayout.ev nev' = some evs ∧
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evs) (ByteString.literal arena)).bind valueOfEvents =
        scalarCanonValueOfBytes evbDoc ∧
      Nonempty EvbCertificate :=
  evb_emission_of_evidence hpre hext
    (evb_evidence_of_spec hpre hext hspec hndst)

/-- **The run and what it leaves.**  The terminating run from the staged entry at
the record's fuel, whose accepting outcome satisfies the call's post and reports
the staged arena cursor, produces the emission.  The run equality is
`evb_run_terminates`'s witness once the verdict is the accepting one; the two
post conditions are the walk's accepted arm, named in this section's docstring. -/
theorem evb_run_to_emission {calls : Calls} {m : Mem} {next ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hrun : runFuel calls (pipelineBudget evbArgs evbMem) JsonPipelineIR.pipelineBody
      (EntryState JsonPipelineIR.pipelineBody evbArgs evbMem (routeNext evbLayout evbDoc)) =
      some (.ret (some (.int 64 1)) m))
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hspec : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m))
    (hndst : readBytes m evbLayout.ndst 8 = some (wordBytes 8 0)) :
    runFuel calls (pipelineBudget evbArgs evbMem) JsonPipelineIR.pipelineBody
        (EntryState JsonPipelineIR.pipelineBody evbArgs evbMem (routeNext evbLayout evbDoc)) =
        some (.ret (some (.int 64 1)) m) ∧
      ∃ (arena evs : List UInt8),
        readBytes m evbLayout.ndst 8 = some (wordBytes 8 ndstU) ∧
        readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
        readBytes m evbLayout.dst ndstU = some arena ∧
        readBytes m evbLayout.ev nev' = some evs ∧
        (eventsOfBytesIndexed (ByteString.literal evbDoc)
            (ByteString.literal evs) (ByteString.literal arena)).bind valueOfEvents =
          scalarCanonValueOfBytes evbDoc ∧
        Nonempty EvbCertificate :=
  ⟨hrun, evb_emission_of_spec hpre hext hspec hndst⟩

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.evb_blocks' does not depend on any axioms -/
#guard_msgs in
#print axioms evb_blocks

/-- info: 'LeanLLVM.Refinement.evb_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evb_budget

/-- info: 'LeanLLVM.Refinement.evb_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_staging

/-- info: 'LeanLLVM.Refinement.evbEvents_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evbEvents_length

/-- info: 'LeanLLVM.Refinement.evb_run_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_run_terminates

/-- info: 'LeanLLVM.Refinement.evb_evidence_of_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_evidence_of_spec

/-- info: 'LeanLLVM.Refinement.evb_emission_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_emission_of_spec

/-- info: 'LeanLLVM.Refinement.evb_run_to_emission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_run_to_emission

/-- info: 'LeanLLVM.Refinement.evb_records_of_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_records_of_rel

/-- info: 'LeanLLVM.Refinement.evb_arena_extent_zero_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_arena_extent_zero_of_evidence

/-- info: 'LeanLLVM.Refinement.evb_emission_of_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_emission_of_evidence

/-- info: 'LeanLLVM.Refinement.evb_events_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_events_of_evidence

/-- info: 'LeanLLVM.Refinement.evbInv_openBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evbInv_openBracket

/-- info: 'LeanLLVM.Refinement.evbInv_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evbInv_number

/-- info: 'LeanLLVM.Refinement.evb_rel_arena_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_rel_arena_free

/-- info: 'LeanLLVM.Refinement.evb_events_of_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_events_of_rel

/-- info: 'LeanLLVM.Refinement.evb_events_of_post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_events_of_post


end LeanLLVM.Refinement
