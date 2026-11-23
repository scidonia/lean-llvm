/-
The route's observation does not need the copy-out.

The adapter's copied result is the eighty-byte header followed by the arena's
used prefix and the event stream (`RouteCall.bytes`).  A no-copy consumer
receives the header alone and reads the two payloads from the staged `dst` and
`ev` arrays between the cursors the header reports.  This module states what
the record's post already fixes about that pair and proves the two readings
coincide:

* the header's words are the projection's words — `verdict`, `nk`, `nxp`,
  `ndst` and `nev` are the slot words `routeResult` reads, and the refusal
  word is the post's `err` slot (on acceptance the slot is unchanged, which at
  the routed staging is the staged zero word);
* the staged arrays' used prefixes are exactly the payloads the copied bytes
  carry, so the two consumers read the same bytes at `[0, ndst)` and
  `[0, nev)`;
* the observation is a function of those two prefixes and nothing else: bytes
  past the used extents are the decoder's slack and the emitters' reserve, and
  the record's `UnchangedOutside` clause names them as the run's whole touched
  region.  `stagedView_extents` states that the view does not observe past
  them.

The semantic content of the payloads — that the event stream decodes to the
parser's tokens — is `Sigma_pipeline`'s and is not restated here; this module
is the byte-level projection of `routePost_outputs`/`routePost_result` at the
route's staging.
-/
import LeanLLVM.JsonCallRoute
import LeanLLVM.JSON.ByteString

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEntrySteps

set_option maxHeartbeats 1000000

/-! ### The staged view -/

/-- The view a no-copy consumer builds from a header and the staged arrays: the
arena is `dst`'s used prefix and the events are `ev`'s, with the same cursors
the header reports. -/
def stagedView (verdict ndst nev : Nat) (dst ev : List UInt8) : RouteView :=
  { verdict := verdict, ndstUsed := ndst, nev := nev,
    arena := dst.take ndst, events := ev.take nev }

/-- **The staged view observes only the used prefixes.**  Two staged pairs whose
used prefixes agree produce the same view, whatever their tails hold: the tail
is outside the extents the header reports. -/
theorem stagedView_extents {verdict ndst nev : Nat} {dst ev dst' ev' : List UInt8}
    (hd : dst.take ndst = dst'.take ndst) (he : ev.take nev = ev'.take nev) :
    stagedView verdict ndst nev dst ev = stagedView verdict ndst nev dst' ev' := by
  simp only [stagedView, hd, he]

/-- **A used prefix is the whole payload.**  When the staged array *is* the
payload, the view's two `take`s are the identity. -/
theorem stagedView_payload (verdict ndst nev : Nat) (arena events : List UInt8)
    (hA : arena.length = ndst) (hE : events.length = nev) :
    stagedView verdict ndst nev arena events =
      { verdict := verdict, ndstUsed := ndst, nev := nev,
        arena := arena, events := events } := by
  simp only [stagedView]
  rw [← hA, ← hE, List.take_length, List.take_length]

/-! ### The post's projection -/

/-- **The header's words, and the staged payloads.**  From the record's post at
the route's arguments, one witness tuple names both: the four slot words the
result reads, the two extents, the refusal word the `err` slot holds, and the
two payloads read at `dst`/`ev`.  The last two lines are the post's own reads,
not a second statement of them.

On acceptance the `err` slot is unchanged by the run; at the routed staging it
holds the eight zero bytes `routeStore` writes, so the witness is zero there.
That is the same word the copied result carries, which is why the no-copy
consumer's `err` needs no separate reading. -/
theorem routePost_observe {l : RouteLayout} {doc : List UInt8} {next : Nat}
    {verdict : BitVec 64} {m : Mem}
    (h : routePost l doc next (.ret (some (.int 64 verdict)) m))
    (hsep : DisjointRegions (stagedExtents l doc)) :
    ∃ (nk' nxp' ndstU nev' err' : Nat) (arena events : List UInt8),
      routeResult (routeArgs l doc) (.ret (some (.int 64 verdict)) m) =
        some { verdict := verdict.toNat, nkWord := wordBytes 8 nk',
               nxpWord := wordBytes 8 nxp', ndstWord := wordBytes 8 ndstU,
               nevWord := wordBytes 8 nev' } ∧
      (verdict.toNat = 0 ∨ verdict.toNat = 1) ∧
      ndstU < 2 ^ 64 ∧ nev' < 2 ^ 64 ∧
      readBytes m l.err 8 = some (wordBytes 8 err') ∧
      readBytes m l.dst ndstU = some arena ∧
      readBytes m l.ev nev' = some events ∧
      arena.length = ndstU ∧ events.length = nev' := by
  simp only [routePost, pipelineUnitsPost, routeArgs] at h
  obtain ⟨hv, nk', nxp', ndstU, ndst', nev', ent, ps, out, evs,
    c, ctype, cst, tok, s, z, e, d, alloc, allocEnd,
    -, hout, hnk, hnxp, -, -, hdst, hev, herr0, herr1, -, -⟩ := h
  simp only [pipelineOutputExtents] at hout
  obtain ⟨hndst64, hnev64, hndst, hnev⟩ := hout
  have hverd : verdict.toNat = 0 ∨ verdict.toNat = 1 := by
    rcases hv with hv | hv <;> rw [hv] <;> decide
  have hres : routeResult (routeArgs l doc) (.ret (some (.int 64 verdict)) m) =
      some { verdict := verdict.toNat, nkWord := wordBytes 8 nk',
             nxpWord := wordBytes 8 nxp', ndstWord := wordBytes 8 ndstU,
             nevWord := wordBytes 8 nev' } := by
    simp only [routeResult, routeArgs, hnk, hnxp, hndst, hnev,
      Option.bind_some, Option.map_some]
  have herr' : ∃ err', readBytes m l.err 8 = some (wordBytes 8 err') := by
    rcases hv with hv | hv
    · exact herr0 hv
    · refine ⟨0, ?_⟩
      rw [herr1 hv]
      have hz : readBytes (stagedMem l doc) l.err 8 = some (List.replicate 8 0) := by
        simpa only [stagedMem, List.length_replicate] using
          (store_read_full (m := []) (mem_err l doc) hsep)
      rw [hz]
      have hw : wordBytes 8 0 = List.replicate 8 0 := by decide
      rw [hw]
  obtain ⟨err', herr'⟩ := herr'
  exact ⟨nk', nxp', ndstU, nev', err', out, evs, hres, hverd, hndst64, hnev64,
    herr', hdst, hev, readBytes_length m l.dst ndstU hdst,
    readBytes_length m l.ev nev' hev⟩

/-! ### The copied bytes and the staged prefixes -/

/-- **The copied result's two payload cuts.**  The adapter's bytes are the
header, then the arena at its used extent, then the events at theirs; the two
cuts the consumers read are the staged payloads. -/
theorem routeCall_extents_eq {c : RouteCall} (hok : c.Lengthed) :
    (c.bytes.drop 80).take c.ndst = c.arena ∧
    (c.bytes.drop (80 + c.ndst)).take c.nev = c.events := by
  obtain ⟨haren, hev⟩ := hok
  have hdrop80 : c.bytes.drop 80 = c.arena ++ c.events := by
    unfold RouteCall.bytes
    rw [List.append_assoc,
      List.drop_append_of_le_length (by rw [routeHeader_length]),
      List.drop_eq_nil_of_le (by simp [routeHeader_length]), List.nil_append]
  have hdropAll : c.bytes.drop (80 + c.ndst) = c.events := by
    rw [← List.drop_drop (i := c.ndst) (j := 80), hdrop80,
      List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append]
  constructor
  · rw [hdrop80, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  · rw [hdropAll, List.take_of_length_le (by omega)]

/-- **The two consumers read the same bytes.**  `copied` is the adapter's
copy-out and `dst`/`ev` are the staged arrays; when the copy is the call's bytes
and each staged array's used prefix is the call's payload, the byte at every
position a consumer reads is the same.  The copy's offsets are `80 + k` and
`80 + ndst + k`; the staged ones are `k`. -/
theorem copied_staged_reads {copied dst ev : ByteString} {c : RouteCall}
    (hok : c.Lengthed)
    (hcopied : copied.toList = c.bytes)
    (hdst : dst.toList.take c.ndst = c.arena)
    (hev : ev.toList.take c.nev = c.events) :
    (∀ k, k < c.ndst → copied[80 + k]? = dst[k]?) ∧
    (∀ k, k < c.nev → copied[80 + c.ndst + k]? = ev[k]?) := by
  obtain ⟨haren, hevents⟩ := hok
  have hdrop80 : c.bytes.drop 80 = c.arena ++ c.events := by
    unfold RouteCall.bytes
    rw [List.append_assoc,
      List.drop_append_of_le_length (by rw [routeHeader_length]),
      List.drop_eq_nil_of_le (by simp [routeHeader_length]), List.nil_append]
  have hdropAll : c.bytes.drop (80 + c.ndst) = c.events := by
    rw [← List.drop_drop (i := c.ndst) (j := 80), hdrop80,
      List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append]
  have htake {bs : ByteString} {n : Nat} {staged : List UInt8}
      (h : bs.toList.take n = staged) {k : Nat} (hk : k < n) :
      bs.toList[k]? = staged[k]? := by
    have h1 : (bs.toList.take n)[k]? = bs.toList[k]? := by
      rw [List.getElem?_take, if_pos hk]
    have h2 : (bs.toList.take n)[k]? = staged[k]? := by rw [h]
    exact h1.symm.trans h2
  constructor
  · intro k hk
    have hdstk : dst.toList[k]? = c.arena[k]? := htake hdst hk
    have hcopyk : copied[80 + k]? = c.arena[k]? := by
      rw [← LeanLLVM.JSON.ByteString.toList_getElem?_eq_getElem?, hcopied,
        ← List.getElem?_drop, hdrop80, List.getElem?_append, if_pos (by omega)]
    rw [hcopyk, ← LeanLLVM.JSON.ByteString.toList_getElem?_eq_getElem?]
    exact hdstk.symm
  · intro k hk
    have hevk : ev.toList[k]? = c.events[k]? := htake hev hk
    have hcopyk : copied[80 + c.ndst + k]? = c.events[k]? := by
      rw [← LeanLLVM.JSON.ByteString.toList_getElem?_eq_getElem?, hcopied,
        ← List.getElem?_drop, hdropAll]
    rw [hcopyk, ← LeanLLVM.JSON.ByteString.toList_getElem?_eq_getElem?]
    exact hevk.symm

/-! ### The no-copy observation -/

/-- **The no-copy observation is the copied one.**  From the record's post, the
call's header and staged extents build a `RouteCall` whose copied bytes decode
to exactly the view a no-copy consumer reads from the staged arrays' used
prefixes.  The two readings are therefore one observation, and the tail past
`ndst`/`nev` is not part of it. -/
theorem routePost_noCopy {l : RouteLayout} {doc : List UInt8} {next : Nat}
    {verdict : BitVec 64} {m : Mem}
    (h : routePost l doc next (.ret (some (.int 64 verdict)) m))
    (hsep : DisjointRegions (stagedExtents l doc)) :
    ∃ c : RouteCall,
      c.verdict = verdict.toNat ∧
      c.arena.length = c.ndst ∧ c.events.length = c.nev ∧
      readBytes m l.err 8 = some (wordBytes 8 c.err) ∧
      readBytes m l.dst c.ndst = some c.arena ∧
      readBytes m l.ev c.nev = some c.events ∧
      (c.bytes.drop 80).take c.ndst = c.arena ∧
      (c.bytes.drop (80 + c.ndst)).take c.nev = c.events ∧
      decodeRouteCall c.bytes =
        some (stagedView c.verdict c.ndst c.nev c.arena c.events) := by
  obtain ⟨nk', nxp', ndstU, nev', err', arena, events, hres, hverd, hndst64,
    hnev64, herr', hdst, hev, hAl, hEl⟩ := routePost_observe h hsep
  -- The adapter's no-copy header: tag 0 accepted / 1 refused, no diagnostic
  -- word, the verdict, the four cursor words and the `err` slot.
  let c : RouteCall :=
    { tag := 1 - verdict.toNat, detail := 0, want := 0, got := 0,
      verdict := verdict.toNat, nk := nk', nxp := nxp', ndst := ndstU,
      nev := nev', err := err', arena := arena, events := events }
  have hok : c.Lengthed := ⟨hAl, hEl⟩
  have hcuts := routeCall_extents_eq hok
  have hdec : decodeRouteCall c.bytes =
      some (stagedView c.verdict c.ndst c.nev c.arena c.events) := by
    rw [stagedView_payload c.verdict c.ndst c.nev c.arena c.events hAl hEl]
    exact decodeRouteCall_bytes c hok (by simpa only [c] using verdict.isLt)
      (by simpa only [c] using hndst64) (by simpa only [c] using hnev64)
  exact ⟨c, rfl, by simpa only [c] using hAl, by simpa only [c] using hEl,
    by simpa only [c] using herr', hdst, hev, hcuts.1, hcuts.2, hdec⟩

end LeanLLVM.Refinement
