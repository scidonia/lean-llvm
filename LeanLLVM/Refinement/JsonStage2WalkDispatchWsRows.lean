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

The class's **arm** is `hcontArm_ws_of_rows`: the cell `.defaultValueHigh × wsByte` in one
theorem, taking the payload, the group, the head's two class bits and the lane row, and
returning `HcontArm.ws` at the produced bundle.  So the group is what the continuing case's
`.ws` branch needs and nothing more.

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
  /-- The seam's three calls, at the class's own seam.  Consumers:
  `hcontWsSeam_of_body`'s `calls` (its first argument) and `hcontScanTail_of_seam`'s. -/
  calls : HcontSeamCalls G (ContTailStartC C)
    (contWsTailStart C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
      b35 k) k x1 x1)
  /-- The kind literal the seam's `phi` selects: `if.else405.i`'s `0`, the arm the run's
  own span leaves the byte at.  Its consumer is `hcontWsSeam_of_body`'s `hcA`. -/
  hcA : calls.cA = BitVec.ofNat 32 0
  /-- The root slot's word as the first call reads it: the seam's memory at `G.next0 + 8`.
  Its consumer is `hcontWsSeam_of_body`'s `hroot` (`HcontWsSeam.hreadRoot`). -/
  hroot : readBytes
    (contWsTailStart C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
      b35 k) k x1 x1).mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)
  /-- The record the tail's scalar call appends.  Its consumers are
  `hcontScanTail_of_seam`'s `ev` and `HcontFacts.ev`. -/
  ev : EventRecord
  /-- The append, at the two calls' memories.  Its consumer is
  `hcontScanTail_of_seam`'s `happ`. -/
  happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
    (TailCarry₂ (ContTailStartC C)).stage.z ev.encodedBytes
  /-- The landing's index cell: the visited byte's number.  Its consumers are
  `hcontFacts_of_staging`'s `q` and `h47`'s `q`. -/
  q : Nat
  /-- The visited byte's bytes.  Its consumer is `hcontFacts_of_staging`'s `bs`, through
  `hbsS`. -/
  bs : List UInt8
  /-- The landing's byte word.  Its consumer is `hcontFacts_of_staging`'s `x47`, through
  `h47`, `hbit47` and `hws47`. -/
  x47 : BitVec 8
  /-- The landing's read, at the tail's endpoint and the stop's index.  This is the
  document's byte at `G.b + k`, read past the tail's stores; its consumer is
  `hcontFacts_of_staging`'s `hreadS`. -/
  hreadS : readBytes
    (contWsEntry C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
      b35 k) k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA).mem
    (G.b + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  /-- The bytes read back as the visit's number.  Its consumer is
  `hcontFacts_of_staging`'s `hbsS`. -/
  hbsS : bytesToNat bs = q
  /-- The landing's `%47` cell.  Its consumer is `hcontFacts_of_staging`'s `h47`. -/
  h47 : evalOperand
    (landRhs457OutAt
      (contWsEntry C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
        b35 k) k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA)
      (BitVec.ofNat 64 k) G.b q) (.reg "%47") = some (.int 8 x47)
  /-- The visited byte is below `13`.  Its consumer is `hcontFacts_of_staging`'s
  `hbit47`. -/
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  /-- And it is `9` or `10`: the scan continues.  Its consumer is
  `hcontFacts_of_staging`'s `hws47`. -/
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  /-- The landing's latch clause at `while.body462.i`: the scan's first visit's block-local
  fact, which is not a consequence of the byte's class (the two `hlastLoc*` lemmas cover the
  other two scan arms and are `True`).  Its consumer is `hcontFacts_of_staging`'s `hlatch`,
  and hence the traversal's round (`walkScanRounds457_of_cell`). -/
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (contWsLatch C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35 k) k
      x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA
      (BitVec.ofNat 64 k) G.b q x47)

/-! ### The whitespace class's group -/

/-- **The whitespace class's remaining rows**, at the class's own reachable states: the
run's own rows at the check state (`run`), the tail's rows (`tail`) and the traversal's
per-index class (`trav`).  The class is `.defaultValueHigh` × `wsByte` — the head's two
clear bits (`slt %8 125 = 0`, `eq %8 125 = 0`, the arm's own class) and the document
byte's whitespace disjunct (`wsStop G (v.toNat - 1)`) — and each field is guarded by the
head's invariant, the continuing count's inequality and the lane row.  **`run` carries the
head byte's two clear bits beside those three**, because its conclusion is `HcontRunBody`,
whose tag bit (`hbit`) is the seam's byte, i.e. the loop head's `%8`: at another byte the
field is false (`hcontRunBody_dash_false`), so the guard is part of its statement.  The
group carries no arm, no bundle and no segment.

* `run`'s consumer is `hcontWsSeam_of_body`'s run segment (`contWsRunBody`), and through it
  `hcontFacts_of_staging`'s `hClass'` and `heicd`;
* `tail`'s consumers are the seam group and `hcontScanTail_of_seam` (the calls, the
  literal, the root word and the record) and `hcontFacts_of_staging`'s landing fields
  (`hreadS`, `hbsS`, `h47`, `hbit47`, `hws47`, `hlatch`);
* `trav`'s consumer is `hcontFacts_of_staging`'s `hbyteClass`.

The two fields the payload cannot reach are named here rather than weakened: the stop's
run and the visits' class are the document's content at windows the payload's row (one
byte at `v - 1`) does not cover, and the landing's class is the scan's first visit and not
the stop's three-way disjunct.

## What the tree produces of the group, and what it does not

`JsonStage2WalkDispatchWsRowsProduce` reduces each field to its remaining supply:

* `run` — the field carries the class's guard (`hlt125`/`hne125`), so
  `hcontRunBody_wsCheck` produces its conclusion from exactly that guard, the entry
  stream's span and the skip's four document rows, with the check state's invariant from
  `contPrefixLand`; `contWsRunBody_at_wsCheck` is the landed counted run (`contWsRunBody`)
  at the body it produces.  The span and the skip are the document's supply — the field's
  own content — while the tag bit and the check state's invariant are derived; the guard is
  load-bearing because at another byte the tag bit cannot clear
  (`hcontRunBody_dash_false`);
* `tail` — `hcontWsTail_of_landing` derives the landing's `%47`, `hbit47` and `hws47` from
  the visited byte being `9` or `10`; the seam's calls, its literal, the root word, the
  record, the read and the latch stay supply;
* `trav` — `hcontWsTravRow_of_bytes` states the field's whole content as the document row
  "every visited byte is `9` or `10`", which is what no producer can supply at a variable
  `G`; the stop's own class does not imply it (`wsVisit_13_false`). -/
structure HcontWsRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The run's own rows at the check state the class's prefix reaches (`HcontRunBody`):
  the stop with its per-index class and budget, the stop's byte, and the seam's byte.  The
  guard is the class's own — the head byte's two clear bits (`slt %8 125 = 0`,
  `eq %8 125 = 0`) — because `HcontRunBody`'s tag bit (`hbit`) is the loop head's `%8` and
  cannot clear at another byte (`hcontRunBody_dash_false`): without the guard the field is
  false.  Its consumer is `hcontWsSeam_of_body`, which derives the run's segment from it. -/
  run : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep →
    evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
    evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
    ∀ (v : BitVec 32),
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
  let b : HcontRunBody G C sl :=
    hw.run C s hInv hblock hk hlt125 hne125 r.v r.hread r.hugt hws
  let tl := hw.tail C s hInv hblock hk r.v b.k
  -- the check state's cells, as the body states them
  have hv : b.v = r.v := by
    have h2 : lookupName sl.env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 r.v.toNat)) :=
      contLandS_cond C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v)
    have h1 := b.hcond
    rw [h2] at h1
    have h4 : (BitVec.ofNat 64 r.v.toNat) = (BitVec.ofNat 64 b.v.toNat) := by
      have h5 := Option.some.inj h1
      simp only [Value.int.injEq, true_and] at h5
      exact eq_of_heq h5
    have h6 := congrArg BitVec.toNat h4
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := b.v.isLt; omega),
      Nat.mod_eq_of_lt (by have := r.v.isLt; omega)] at h6
    exact (BitVec.eq_of_toNat_eq h6).symm
  have hix : b.ix = contIx G C := by
    have h1 := b.hidx
    have h2 : lookupName sl.env "%idxprom.i" =
        some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := b.hInv.idx_reg
    rw [h2] at h1
    have h4 : BitVec.ofNat 64 (entryPos G C.k) = b.ix := by
      have h5 := Option.some.inj h1
      simp only [Value.int.injEq, true_and] at h5
      exact eq_of_heq h5
    exact h4.symm
  have hb35 : b.b35 = contB35 G r.v := by
    have h1 := b.h35
    simp only [evalOperand] at h1
    have h2 : lookupName sl.env "%35" = some (.int 8 (cont35 (contB35 G r.v))) :=
      contLandS_35 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v)
    rw [h2] at h1
    have h4 : cont35 (contB35 G r.v) = cont35 b.b35 := by
      have h5 := Option.some.inj h1
      simp only [Value.int.injEq, true_and] at h5
      exact eq_of_heq h5
    have h6 := congrArg BitVec.toNat h4
    rw [cont35, cont35, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := (contB35 G r.v).toNat_lt; omega),
      Nat.mod_eq_of_lt (by have := b.b35.toNat_lt; omega)] at h6
    exact (UInt8.toNat_inj.mp h6).symm
  have hx1 : b.x1 = hlastByte G C := by
    have h1 := b.h8c
    simp only [evalOperand] at h1
    have h2 : lookupName
        (contWsSeamS C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1).env "%8" =
        lookupName (wsSlAt G sl b.b35 b.ix b.v b.k).env "%8" :=
      seamS_env8 _ _ _ _
    rw [h2] at h1
    have h3 : lookupName (wsSlAt G sl b.b35 b.ix b.v b.k).env "%8" =
        some (.int 8 (hlastByte G C)) := by
      have hsl : wsSlAt G sl b.b35 b.ix b.v b.k =
          wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
            (contB35 G r.v) b.k := by
        rw [hb35, hix, hv]
        exact wsSlAt_transport G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep r.v
          (contIx G C) (contB35 G r.v) b.k
      rw [hsl, wsSlS_env8]
      exact hInv.iter.reg8
    rw [h3] at h1
    have h4 : hlastByte G C = b.x1 := by
      have h5 := Option.some.inj h1
      simp only [Value.int.injEq, true_and] at h5
      exact eq_of_heq h5
    exact h4.symm
  -- the run's body at the group's own terms: the stop, the byte and the check state's
  -- cells are pinned to the lane row's, so the seam's states are the group's
  let bG : HcontRunBody G C sl :=
    { hInv := b.hInv, b35 := contB35 G r.v, h35 := by rw [← hb35]; exact b.h35,
      ix := contIx G C, hidx := by rw [← hix]; exact b.hidx,
      v := r.v, hcond := by rw [← hv]; exact b.hcond,
      hugt := by rw [← hv, ← hix]; exact b.hugt,
      k := b.k, x1 := hlastByte G C,
      hClass := by rw [← hb35, ← hv, ← hix]; exact b.hClass,
      heicd := by rw [← hv]; exact b.heicd,
      h8c := by rw [← hx1, ← hb35, ← hix, ← hv]; exact b.h8c,
      hbit := by rw [← hx1]; exact b.hbit,
      hspan := by rw [← hv]; exact b.hspan }
  -- the class, from the run's own rows
  have hClass' : wsStop G (r.v.toNat - 1) ∧
      (∀ q, entryPos G C.k ≤ q → q < b.k → wsCont G q) ∧ wsStop G b.k ∧
      entryPos G C.k < b.k ∧ r.v.toNat - entryPos G C.k ≤ C.inner := by
    obtain ⟨-, hrun, hstop, hik, hbud, -⟩ := bG.hClass
    have hix' : (contIx G C).toNat = entryPos G C.k := contIx_toNat G C hk
    refine ⟨hws, ?_, hstop, ?_, ?_⟩
    · intro q hq1 hq2
      exact hrun q (by rw [hix']; exact hq1) hq2
    · rw [hix'] at hik
      exact hik
    · rw [hix'] at hbud
      exact hbud
  -- the second byte's class, from the head byte's two clear bits
  have h8c : evalOperand
      (contWsSeamS C (contWsSlStaging G C s r.v (contIx G C) (contB35 G r.v) b.k) b.k
        (hlastByte G C)) (.reg "%8") = some (.int 8 (hlastByte G C)) := by
    simp only [evalOperand, contWsSeamS, contWsSlStaging]
    rw [seamS_env8, wsSlS_env8]
    exact LeanLLVM.evalOperand_reg_of hInv.iter.reg8
  -- the tail: the seam group from the run's rows and the class's bits, then the three
  -- links.  The group's own tail is at exactly those states, so no state is transported.
  have hc110 : evalICmp .slt bG.x1 (BitVec.ofNat 8 110) = 0 :=
    hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hc116 : evalICmp .slt bG.x1 (BitVec.ofNat 8 116) = 0 :=
    hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hceq116 : evalICmp .eq bG.x1 (BitVec.ofNat 8 116) = 0 :=
    hlast_eq_zero_of_slt_zero (by decide) hlt125
  have seam : HcontWsSeam G C sl bG tl.calls :=
    hcontWsSeam_of_body G C sl bG hk tl.calls hc110 hc116 hceq116 tl.hcA tl.hroot
  have hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (contWsSlStaging G C s r.v (contIx G C) (contB35 G r.v) b.k) b.k
        (hlastByte G C) (hlastByte G C))
      (TailCarryScan (ContTailStartC C) tl.ev)
      (contWsEntry C (contWsSlStaging G C s r.v (contIx G C) (contB35 G r.v) b.k) b.k
        (hlastByte G C) (hlastByte G C) tl.calls.r₁ tl.calls.r₂ tl.calls.r₃ b.k r.v
        tl.calls.cA tl.calls.rdv tl.calls.xA) 3 :=
    hcontScanTail_of_seam G C sl bG tl.calls seam tl.ev tl.happ
  -- the bundle
  refine hcontFacts_of_staging G C s hInv hk hlt125 hne125 (v := r.v) ?_ ?_ (k := b.k)
    hClass' h8c tl.calls.r₁ tl.calls.r₂ tl.calls.r₃ tl.ev (cA := tl.calls.cA)
    (rdv := tl.calls.rdv) (xA := tl.calls.xA) hTail (q := tl.q) (bs := tl.bs)
    (x47 := tl.x47) ?_ tl.hbsS ?_ tl.hbit47 tl.hws47 tl.hlatch r.hvle
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

/-! ### The class's arm, from the payload and the group -/

/-- **The whitespace class's continuing arm, from the payload and the group.**  This is the
`.defaultValueHigh` × `wsByte` cell of the continuing class case in one theorem: the head's
byte is `126` or `127` (the class's two clear bits) and the document byte before the entry's
end is whitespace (the group's guard), so the arm is `HcontArm.ws` at
`hcontFacts_of_rows`'s bundle.  Neither input is an arm, and the tail the bundle carries is
the producer's conclusion from the group's three call rows, so this cell takes no segment. -/
noncomputable def hcontArm_ws_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hp : HcontPayload G) (hw : HcontWsRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .ws (hcontFacts_of_rows hp hw C s hInv hblock hk hlt125 hne125 r hws)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.wsSlS_env8
#print axioms LeanLLVM.Refinement.WalkScope.hcontFacts_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_ws_of_rows

end WalkScope
end LeanLLVM.Refinement
