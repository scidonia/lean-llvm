/-
# The whitespace class's rows, and its bundle from the payload

`HcontFacts` (`JsonStage2WalkRevolution`) is the continuing entry's **whitespace** bundle:
the class whose byte before the entry's end is `9`, `10`, `13` or `32`, so the skip runs,
the token ends at the first whitespace byte `k`, and the extra-token scan runs `[k, v)`
with `k < v`.  Its producer is `hcontFacts_of_staging`
(`JsonStage2WalkHcontFactsOfStaging`), and its remaining arguments are what the payload
(`HcontPayload`, `JsonStage2WalkDispatchSupply`) does not carry: the skip's stop and its
class beyond `v - 1`, the tail's landing, the traversal's per-index class and the seam's
three calls.

This module states those rows as one group — `HcontWsRows` — and produces the bundle from
the payload and the group (`hcontFacts_of_rows`).  The group is a set of facts about the
document and the call environment at the states the class's own prefix reaches; it carries
no arm, no bundle and no segment.

## What the payload gives, and what the group adds

The payload's `lane.defaultLane` states the next entry's lane word and its read, the
bound's compare and the byte before the entry's end with its class.  From it the producer
derives:

* the lane read at the state the head's own blocks leave (`contAS₅`'s memory is the head's,
  and the header's increment is `C.k + 1` — `cont_inc_toNat`), and the order test
  (`HcontDefaultRow.hugt` is stated at `contIx`, which *is* the entry's position word);
* the byte before the entry's end, `contB35 G v`, and the entry's end's bound (`hvle`);
* the skip's *class at `v - 1`*: the payload's `defaultLane` row carries its
  `HcontByteClass`, and this group is guarded by the `.wsByte` disjunct
  (`wsStop G (v.toNat - 1)`), which is the class's own selector.

What the payload cannot give is the run past that byte:

* `run` — the run's own rows at the class's check state (`HcontRunBody`): the stop `k`, the
  per-index class `[entryPos C.k, k)`, the stop's byte class, the inner budget the first
  visit spends, the seam's byte and the span.  The payload's `hclass` names the byte at
  `v - 1` only, and the skip continues from the entry's first byte, so the stop and the run
  are the document's — a row, not a consequence;
* `tail` — the seam's three callee rows with their kind literal, the root slot's word at
  the seam, the record the scalar call appends, and the landing's byte with its class.
  These are the call environment's and the document's; the tail's **segment** is not here:
  it is `hcontScanTail_of_seam`'s conclusion from these rows and the seam group
  (`HcontWsSeam`, built by `hcontWsSeam_of_body` from `run` and the class-C span);
* `trav` — the traversal's per-index class on the visits' window `[k + 1, v)`.  **This row
  cannot be produced from the skip's class and the bounded window**: the skip's class is
  the document's bytes on `[entryPos C.k, k)`, and the visits' class is its bytes on
  `[k + 1, v)`.  The two windows are disjoint, the document is arbitrary, and the stop's
  own byte (at `k`) does not decide the later ones — `wsStop` admits `13` and `32`, while
  the visits' class is the `9`/`10` arm.  So the row is the document's and is named here;
  it is the same row `hcontFacts_of_staging` already takes as `hbyteClass`, at the span
  `k < p + 1` that `JsonStage2WalkRevolutionScanRound`'s `scanByteField` reads.

The landing's class is the document's for the same reason: the first visited byte is the
stop's (`wsStop` at `k`), but the scan's first visit is decided by the `%47` arm, which is
the `9`/`10` class — one of the stop's three disjuncts and not a consequence of the other
two.

## The tail, produced and not taken

`hcontFacts_of_staging` takes the tail as a `WalkSegment`.  Here it is a conclusion: the
group's `tail` states the three callee rows (`HcontSeamCalls`) and the literal the seam
stores, the group's `run` gives the run's segment (`contWsRunBody`), and `hcontWsSeam_of_body`
turns those into the seam's invariant and cells.  `hcontScanTail_of_seam` then composes the
three links to the scan's entry.  So the producer establishes the tail; no field carries it.

## The states

The class's prefix reaches `contLandS` — the `NodeBlock41` check state — at the head's own
byte and counts; `wsCheckS` names it.  The stop is `wsSlS` at that check state, which is
`wsSlAt` at it (`wsSlAt_transport`).  The seam is `contWsTailStart` at the stop, and the
tail's target is `contWsEntry`.  Every row below is stated at those states, so the group's
fields are the class's own reachable states and not a wider `∀` over heads.
-/
import LeanLLVM.Refinement.JsonStage2WalkHcontFactsOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The class's states -/

/-- The check state the whitespace class's prefix reaches: `NodeBlock41`, at the head's
byte, counts and lane word. -/
abbrev wsCheckS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (v : BitVec 32) : State :=
  contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
    (contB35 G v)

/-- `%8` at the stop state is the loop head's byte: the skip's blocks and the latch bind
their own cells and none of them is `%8`. -/
theorem wsSlS_env8 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (k : Nat) :
    lookupName (wsSlS G C s x inc nep ep v ix b35 k).env "%8" =
      lookupName s.env "%8" := by
  have hpre : lookupName (wsPreS G C s x inc nep ep v ix b35).env "%8" =
      lookupName s.env "%8" := by
    rw [← wsPreSAt_transport]
    rw [wsPreSAt_env8, contLandS_env8]
  simp only [wsSlS, wsStopAt_env8, wsLeafS_env8, landRhsPreheaderOutAt]
  exact hpre

/-! ### The tail's rows

The seam's three callee rows with the kind literal they store, the root slot's word as the
first call reads it, the record the scalar call appends, and the landing's byte with its
class — all at the states the class's prefix, the run's stop and the seam name.  The
structure carries no segment: the tail is `hcontScanTail_of_seam`'s conclusion from it.
-/
structure HcontWsTail {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (v : BitVec 32) (b35 : UInt8) (ix : BitVec 64) (k : Nat) (x1 : BitVec 8) : Type where
  /-- The seam's three calls, at the class's own seam. -/
  calls : HcontSeamCalls G (ContTailStartC C)
    (contWsTailStart C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
      b35 k) k x1 x1)
  /-- The kind literal the seam's `phi` selects: `if.else405.i`'s `0`, the arm the run's
  own span leaves the byte at. -/
  hcA : calls.cA = BitVec.ofNat 32 0
  /-- The root slot's word as the first call reads it: the seam's memory at `G.next0 + 8`.
  Its consumer is `hcontWsSeam_of_body`'s `hroot` (`HcontWsSeam.hreadRoot`). -/
  hroot : readBytes
    (contWsTailStart C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
      b35 k) k x1 x1).mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)
  /-- The record the tail's scalar call appends.  Its consumer is `hcontScanTail_of_seam`'s
  `happ` and `HcontFacts.ev`. -/
  ev : EventRecord
  /-- The append, at the two calls' memories. -/
  happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
    (TailCarry₂ (ContTailStartC C)).stage.z ev.encodedBytes
  /-- The landing's index cell: the visited byte's number. -/
  q : Nat
  /-- The visited byte's bytes. -/
  bs : List UInt8
  /-- The landing's byte word. -/
  x47 : BitVec 8
  /-- The landing's read, at the tail's endpoint and the stop's index.  This is the
  document's byte at `G.b + k`, read past the tail's stores; its consumer is
  `hcontFacts_of_staging`'s `hreadS`. -/
  hreadS : readBytes
    (contWsEntry C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
      b35 k) k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA).mem
    (G.b + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  /-- The bytes read back as the visit's number. -/
  hbsS : bytesToNat bs = q
  /-- The landing's `%47` cell. -/
  h47 : evalOperand
    (landRhs457OutAt
      (contWsEntry C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
        b35 k) k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA)
      (BitVec.ofNat 64 k) G.b q) (.reg "%47") = some (.int 8 x47)
  /-- The visited byte is below `13`. -/
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  /-- And it is `9` or `10`: the scan continues. -/
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1

/-! ### The whitespace class's group -/

/-- **The whitespace class's remaining rows**, at the class's own reachable states: the
run's own rows at the check state (`run`), the tail's rows (`tail`) and the traversal's
per-index class (`trav`).  The group carries no arm, no bundle and no segment, and each
field is guarded by the class's guard — the head's invariant, the continuing count's
inequality, the lane row and the document byte's `.wsByte` disjunct where the field is
stated at that row's word.

* `run`'s consumer is `hcontWsSeam_of_body`'s run segment (`contWsRunBody`), and through it
  `hcontFacts_of_staging`'s `hClass'` and `heicd`;
* `tail`'s consumers are the seam group and `hcontScanTail_of_seam` (the calls, the
  literal, the root word and the record) and `hcontFacts_of_staging`'s landing fields
  (`hreadS`, `hbsS`, `h47`, `hbit47`, `hws47`);
* `trav`'s consumer is `hcontFacts_of_staging`'s `hbyteClass`.

The two fields the payload cannot reach are named here rather than weakened: the stop's
run and the visits' class are the document's content at windows the payload's row (one
byte at `v - 1`) does not cover, and the landing's class is the scan's first visit and not
the stop's three-way disjunct. -/
structure HcontWsRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The run's own rows at the check state the class's prefix reaches (`HcontRunBody`):
  the stop with its per-index class and budget, the stop's byte, and the seam's byte.  Its
  consumer is `hcontWsSeam_of_body`, which derives the run's segment from it. -/
  run : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → ∀ (v : BitVec 32),
    readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some (natToBytes v.toNat 4) →
    evalICmp .ugt (BitVec.ofNat 64 v.toNat) (contIx G C) = 1 →
    wsStop G (v.toNat - 1) → HcontRunBody G C (wsCheckS G C s v)
  /-- The tail's rows at the class's seam: the three calls with their literal, the root
  word, the appended record and the landing. -/
  tail : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → ∀ (v : BitVec 32) (k : Nat),
    HcontWsTail G C s v (contB35 G v) (contIx G C) k (hlastByte G C)
  /-- The traversal's per-index class on the visits' window `[k + 1, v)`.  This is the
  document's row and is not produced from the skip's class: the two windows are disjoint
  and the document is arbitrary (see this module's header). -/
  trav : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → ∀ (v : BitVec 32) (k : Nat) p, k < p + 1 → p + 1 < v.toNat →
    (evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)

/-! ### The bundle from the payload and the group -/

/-- **The whitespace bundle, produced.**  The lane read, the order test, the span and the
second byte's class are derived from the payload's row and the invariant; the class is the
group's `run`; the tail is `hcontScanTail_of_seam`'s from the group's `tail` and the seam
group; the traversal's class is the group's `trav`.  So the one segment the bundle carries
is the producer's conclusion, and no field of the group is it.

The four pinning facts the composition reads are the check state's cells: the body's
`%cond350.i`, `%35` and `%idxprom.i` are the head's own (`contLandS_cond`, `contLandS_35`
and `WalkInv.idx_reg`), and its `%8` is `hlastByte G C` (`wsSlS_env8` through
`seamS_env8`).  With them `b.v = v`, `b.b35 = contB35 G v`, `b.ix = contIx G C` and
`b.x1 = hlastByte G C`, so every state the bundle names is the group's. -/
noncomputable def hcontFacts_of_rows {m0 : Mem} {G : WalkGeom m0} (hp : HcontPayload G)
    (hw : HcontWsRows G) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1)) :
    HcontFacts G C s := by
  let sl := wsCheckS G C s r.v
  let b := hw.run C s hInv hblock hk r.v r.hread r.hugt hws
  let tl := hw.tail C s hInv hblock hk r.v b.k
  -- the check state's cells, as the body states them
  have hv : b.v = r.v := by
    have h2 : lookupName sl.env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 r.v.toNat)) :=
      contLandS_cond C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v)
    have h1 := b.hcond
    rw [h2] at h1
    have h4 : (BitVec.ofNat 64 b.v.toNat) = (BitVec.ofNat 64 r.v.toNat) := by
      have h5 := Option.some.inj h1
      simpa only [Value.int.injEq, and_true] using h5
    have h6 := congrArg BitVec.toNat h4
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := b.v.isLt; omega),
      Nat.mod_eq_of_lt (by have := r.v.isLt; omega)] at h6
    exact BitVec.eq_of_toNat_eq h6
  have hix : b.ix = contIx G C := by
    have h1 := b.hidx
    have h2 : lookupName sl.env "%idxprom.i" =
        some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := b.hInv.idx_reg
    rw [h2] at h1
    have h4 : b.ix = BitVec.ofNat 64 (entryPos G C.k) := by
      have h5 := Option.some.inj h1
      simpa only [Value.int.injEq, and_true] using h5
    exact h4
  have hb35 : b.b35 = contB35 G r.v := by
    have h1 := b.h35
    simp only [evalOperand] at h1
    have h2 : lookupName sl.env "%35" = some (.int 8 (cont35 (contB35 G r.v))) :=
      contLandS_35 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v)
    rw [h2] at h1
    have h4 : cont35 b.b35 = cont35 (contB35 G r.v) := by
      have h5 := Option.some.inj h1
      simpa only [Value.int.injEq, and_true] using h5
    have h6 := congrArg BitVec.toNat h4
    rw [cont35, cont35, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := b.b35.toNat_lt; omega),
      Nat.mod_eq_of_lt (by have := (contB35 G r.v).toNat_lt; omega)] at h6
    exact UInt8.toNat_inj.mp h6
  have hx1 : b.x1 = hlastByte G C := by
    have h1 := b.h8c
    simp only [evalOperand] at h1
    have h2 : lookupName
        (contWsSeamS C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v
          (contIx G C) (contB35 G r.v) b.k) b.k b.x1).env "%8" =
        lookupName (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v
          (contIx G C) (contB35 G r.v) b.k).env "%8" :=
      seamS_env8 _ _ _ _
    rw [h2] at h1
    have h3 : lookupName
        (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
          (contB35 G r.v) b.k).env "%8" = some (.int 8 (hlastByte G C)) := by
      rw [wsSlS_env8]
      exact hInv.iter.reg8
    rw [h3] at h1
    have h4 : b.x1 = hlastByte G C := by
      have h5 := Option.some.inj h1
      simpa only [Value.int.injEq, and_true] using h5
    exact h4
  -- the class, from the run's own rows
  have hClass' : wsStop G (r.v.toNat - 1) ∧
      (∀ q, entryPos G C.k ≤ q → q < b.k → wsCont G q) ∧ wsStop G b.k ∧
      entryPos G C.k < b.k ∧ r.v.toNat - entryPos G C.k ≤ C.inner := by
    obtain ⟨-, hrun, hstop, hik, hbud, -⟩ := b.hClass
    have hix' : b.ix.toNat = entryPos G C.k := by rw [hix]; exact contIx_toNat G C hk
    refine ⟨hws, ?_, hstop, ?_, ?_⟩
    · intro q hq1 hq2
      exact hrun q (by omega) hq2
    · omega
    · rw [hv]; omega
  -- the second byte's class, from the head byte's two clear bits
  have h8c : evalOperand
      (contWsSeamS C (contWsSlStaging G C s r.v (contIx G C) (contB35 G r.v) b.k) b.k
        (hlastByte G C)) (.reg "%8") = some (.int 8 (hlastByte G C)) := by
    simp only [evalOperand, contWsSeamS, contWsSlStaging]
    rw [seamS_env8, wsSlS_env8]
    exact hInv.iter.reg8
  -- the tail: the seam group from the run's rows and the class's bits, then the three
  -- links
  have hc110 : evalICmp .slt b.x1 (BitVec.ofNat 8 110) = 0 := by
    rw [hx1]; exact hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hc116 : evalICmp .slt b.x1 (BitVec.ofNat 8 116) = 0 := by
    rw [hx1]; exact hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hceq116 : evalICmp .eq b.x1 (BitVec.ofNat 8 116) = 0 := by
    rw [hx1]; exact hlast_eq_zero_of_slt_zero (by decide) hlt125
  have hcalls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1) := by
    rw [hb35, hix, hv, hx1, wsSlAt_transport]
    exact tl.calls
  have hroot : readBytes
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).mem
      (G.next0 + 8) 4 = some (natToBytes hcalls.rdv.toNat 4) := by
    rw [hb35, hix, hv, hx1, wsSlAt_transport]
    exact tl.hroot
  have seam : HcontWsSeam G C sl b hcalls :=
    hcontWsSeam_of_body G C sl b hk hcalls hc110 hc116 hceq116 tl.hcA hroot
  have hTailAt : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1)
      (TailCarryScan (ContTailStartC C) tl.ev)
      (contWsEntry C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1 hcalls.r₁ hcalls.r₂
        hcalls.r₃ b.k b.v hcalls.cA hcalls.rdv hcalls.xA) 3 :=
    hcontScanTail_of_seam G C sl b hcalls seam tl.ev tl.happ
  have hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (contWsSlStaging G C s r.v (contIx G C) (contB35 G r.v) b.k) b.k
        (hlastByte G C) (hlastByte G C))
      (TailCarryScan (ContTailStartC C) tl.ev)
      (contWsEntry C (contWsSlStaging G C s r.v (contIx G C) (contB35 G r.v) b.k) b.k
        (hlastByte G C) (hlastByte G C) hcalls.r₁ hcalls.r₂ hcalls.r₃ b.k r.v hcalls.cA
        hcalls.rdv hcalls.xA) 3 := by
    simpa only [wsCheckS, contWsSlStaging, hb35, hix, hv, hx1, wsSlAt_transport] using hTailAt
  -- the bundle
  refine hcontFacts_of_staging G C s hInv hk hlt125 hne125 (v := r.v) ?_ ?_ (k := b.k)
    hClass' h8c hcalls.r₁ hcalls.r₂ hcalls.r₃ tl.ev (cA := hcalls.cA)
    (rdv := hcalls.rdv) (xA := hcalls.xA) hTail (q := tl.q) (bs := tl.bs)
    (x47 := tl.x47) ?_ tl.hbsS ?_ tl.hbit47 tl.hws47 r.hvle
    (hbyteClass := hw.trav C s hInv hblock hk r.v b.k)
  · -- the lane read, at the state the head's blocks leave
    rw [show (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem = s.mem from rfl,
      cont_inc_toNat G C hk]
    exact r.hread
  · -- the order test, at the entry's own position word
    exact r.hugt
  · -- the landing's read
    exact tl.hreadS
  · -- the landing's `%47`
    exact tl.h47

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.wsSlS_env8
#print axioms LeanLLVM.Refinement.WalkScope.hcontFacts_of_rows

end WalkScope
end LeanLLVM.Refinement
