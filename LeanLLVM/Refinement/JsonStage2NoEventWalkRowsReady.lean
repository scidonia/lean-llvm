/-
The no-event walk's container producers, with the route's staging derived at a head.

`JsonStage2NoEventWalkRowsAssemble` reduces the bracket and brace classes to the
committed empty-pair rows (`stage2NoEventWalkRow_cont_bracketPair`,
`stage2NoEventWalkRow_cont_bracePair`) at the classes' producer predicates, and
leaves every route-staging fact as an argument.  This module derives the staging
at a head and states each producer at its minimal remaining premises.

**What is derived.**  At `Head K mem k s` with the class predicate:

* the closer's entry — `K.ent[k+1]? = some next` and `K.bs[next]? = some
  nextByte` — from `Inv.entries` with `K.ent.length = K.nep`
  (`readLanes32_length`), the room `k + 2 ≤ K.nep`, and `Inv.inside`;
* the post-push entry read — `readBytes (writeBytes … (bracketPushAddr …) …) (K.ep
  + (k+1)·4) 4 = some bs4` and `bytesToNat bs4 < 2^32` — from
  `readLanes32_lane` at the head's own memory and `readBytes_writeBytes_frame`,
  the push landing in the stack region;
* the document's byte at that entry — `readBytes (writeBytes …) (K.b + next) 1 =
  some [nextByte]` — from `Inv.docByte` and the same frame;
* the pop read — `readBytes (writeBytes … (push) …) (pop) 1 = some bs` with
  `bs.length = 1` and `bytesToNat bs = fr` — the pop address *is* the push
  address, so the read is of the written byte (`readBytes_writeBytes_same`), and
  the frame's byte is `fr` because `fr < 2^8`;
* the index facts `k + 3 < 2^63` (from `Inv.nepLe` and `Inv.maxDoc`).

**What resists, and why.**  The facts that remain are *branch guards* of the
routes: the predicates that select a route's branch, not consequences of the
head.  Each is stated in the branch's own form (`sp ≠ 0` rather than `1 ≤ sp`),
and at the seed's head both forms are false — `Seed`'s
`loopHeadPhiCellsAt K 0 0 0 0 520` binds depth and frame to zero, so the depth is
`0`, and on `Nat` `(sp ≠ 0) ↔ (1 ≤ sp)`: the guard is false there because it
names a branch the seed is not on, not because the exclusion form escapes the
seed.  Which branch a head is on is the producer's case split
(`…Ready_of_arms` below), never a claim about every head:

* `nextByte.toNat = 93` (bracket) / `125` (brace) — the empty-pair route is the
  closer arm of `if.end327.peel`/`close_obj`; at a `[`/`{` head whose next entry
  opens a value the walk descends instead, and the committed bytes carry no row
  for that branch.  No lemma relates `K.ent` to the after-value table
  (`Stage2NoEventAfterValueClass` has no producer at an entry index); the missing
  statement is `Stage2NoEventWalkHeadBracketClass.closer` /
  `…BraceClass.closer`.
* `sp ≠ 0` and `sp ≤ 519` — `Head.layers` binds `sp < 2^32` only; the stack's
  520-byte extent is `Inv.stagedBytes`' presence, not a bound on the register.
  The push route states the pair as its own guard
  (`stage2NoEventWalkContainerPushBracket`'s `hroom`).  The seed head has
  `sp = 0`, so the guard is false there and the depth-zero head belongs to the
  terminal lane (`JsonStage2NoEventWalkRowsContainerZero`); the committed row's
  `1 ≤ sp` is the same `Nat` statement (`Nat.pos_of_ne_zero`), not a weaker
  claim that survives the seed.  `sp ≤ 519` is the route's own test
  (`%exitcond.peel` for the bracket, `%cmp10` for the brace).
* `fr ≠ 0` — the frame-zero head is the same terminal lane's, so this too is
  false at the seed.  The committed pair rows take `1 ≤ fr`, the same `Nat`
  statement as the guard.
* the comma `∀ q, K.ent[k+2]? = some q → K.bs.getD q 0 = 44` — `Inv.doc` gives
  the document byte's *presence* at an entry, never its value: the separator is
  the cycle's own read at the endpoint.  The missing statement is
  `Stage2NoEventWalkInv.commaAt`.
* the next head's liveness `k + 3 < K.nep` — a `Head` carries `k < K.nep` only.
  Its negation is the depth-0 / trailing-entry terminal lane, whose
  `Stage2NoEventWalkExit` evidence (`Stage2NoEventRun` report and
  `stage2NoEventBoundary`) is the caller's post, carried by neither `Head` nor
  `Trace`; the missing statement is `Stage2NoEventWalkHead.continues`.  A
  producer at `Stage2NoEventWalkRow` cannot derive the negation, so it cases the
  arm and takes the terminal row as its premise (`…Ready_of_arms`).

The live arm's producer therefore takes exactly those facts — the shared
`Stage2NoEventWalkPairBranch` beside each class's closer byte
(`Stage2NoEventWalkBracketGuard`/`…BraceGuard`) — and nothing else: every memory
read and index bound the committed rows take is derived here.  The terminal arm's
producer takes the class's terminal row, whose post evidence is the caller's.
The carry's `%xj = K.next0` is **not** among either arm's premises: it is the
invariant's static equality (`Stage2NoEventWalkInv.xjNext0`), projected at a head
as `Stage2NoEventWalkHead.xjNext0`, so no producer takes it beside the head.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsAssemble
import LeanLLVM.Refinement.JsonStage2NoEventWalkValue

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps
  (readBytes_writeBytes_frame readBytes_length)

/-! ### The head's depth and frame cells, with their widths

`Head.spPhi` projects the three cells; the pair routes also need the widths the
push address's arithmetic uses, which `Head.layers` carries.  This projection
states both at one set of witnesses. -/

/-- **The head's depth, frame and zero extension, with their widths.** -/
theorem Stage2NoEventWalkHead.spPhiBounded {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ (sp fr : Nat),
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) ∧
      lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)) ∧
      lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)) ∧
      sp < 2 ^ 32 ∧ fr < 2 ^ 8 := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -, -, -, -, hspLt, hfrLt,
    hone, -⟩ := h.layers
  have hspH : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  have hfrH : lookupName s.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  have h1Hone : lookupName s.env "%1" =
      some (.int 64 (BitVec.ofNat 64 one)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  exact ⟨sp, fr, hspH, hfrH, by simpa [hone] using h1Hone, hspLt, hfrLt⟩

/-! ### The closer's entry

The pair route reads the entry at `k + 1` and the document's byte there.  Both
are consequences of the head's entry stream and its document. -/

/-- **A head with room for two more entries has one at `k + 1`.** -/
theorem Stage2NoEventWalkHead.entSucc {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s)
    (hk : k + 2 ≤ K.nep) : ∃ next, K.ent[k + 1]? = some next := by
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hi : k + 1 < K.ent.length := by rw [hlen]; omega
  exact ⟨K.ent[k + 1], List.getElem?_eq_getElem hi⟩

/-- **The document's byte at an entry.**  An entry is inside the document
(`Inv.inside`), and the document is the read's list (`Inv.doc`). -/
theorem Stage2NoEventWalkInv.docGetElem? {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {q : Nat} (hq : q < K.n) :
    ∃ b, K.bs[q]? = some b := by
  have hlen : K.bs.length = K.n := readBytes_length mem K.b K.n h.doc
  have hi : q < K.bs.length := by rw [hlen]; exact hq
  exact ⟨K.bs[q], List.getElem?_eq_getElem hi⟩

/-- **The closer's entry and its byte**, from the head's entry stream and
document. -/
theorem Stage2NoEventWalkHead.closerEntry {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s)
    (hk : k + 2 ≤ K.nep) :
    ∃ next nextByte, K.ent[k + 1]? = some next ∧ K.bs[next]? = some nextByte := by
  obtain ⟨next, hk1⟩ := h.entSucc hk
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  obtain ⟨nextByte, hbs1⟩ := h.inv.docGetElem? hnextLt
  exact ⟨next, nextByte, hk1, hbs1⟩

/-! ### The push and pop addresses

Both routes push one frame byte below the depth (`%stk + (%sp − 1)`) and the pop
reads at that same address through a second computation (`closeReadAddr`).  The
arithmetic is the two routes' address forms, stated once. -/

/-- **The bracket push's address is `%stk + (%sp − 1)`.** -/
theorem stage2NoEventWalkBracketPushAddr_eq (K : Stage2NoEventWalkCarry) {sp : Nat}
    (h1 : 1 ≤ sp) (h2 : sp < 2 ^ 32) :
    bracketPushAddr K (BitVec.ofNat 64 sp) = K.stk + (sp - 1) := by
  unfold bracketPushAddr
  rw [stage2NoEventStoreAddr64 (a := BitVec.ofNat 64 sp) (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sp < 2 ^ 64)]
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sp < 2 ^ 64)]

/-- **The brace push's address is `%stk + (%sp − 1)`.** -/
theorem stage2NoEventWalkBracePushAddr_eq (K : Stage2NoEventWalkCarry) {sp : Nat}
    (h1 : 1 ≤ sp) (h2 : sp < 2 ^ 32) :
    bracePushAddr K (BitVec.ofNat 32 sp) = K.stk + (sp - 1) := by
  unfold bracePushAddr
  rw [stage2NoEventStoreAddr (sp := BitVec.ofNat 32 sp) (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]

/-- **The brace pop's address is `%stk + (%sp − 1)`**, the push's address. -/
theorem stage2NoEventWalkBracePopAddr_eq (K : Stage2NoEventWalkCarry) {sp : Nat}
    (h1 : 1 ≤ sp) (h2 : sp < 2 ^ 32) :
    bracePopAddr K sp = K.stk + (sp - 1) := by
  unfold bracePopAddr
  have hsp32 : (BitVec.ofNat 32 sp).toNat = sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
  have hconst : (BitVec.ofNat 32 1 + BitVec.ofNat 32 4294967294) =
      BitVec.ofNat 32 4294967295 := by decide
  have hassoc : (BitVec.ofNat 32 sp + BitVec.ofNat 32 1) + BitVec.ofNat 32 4294967294 =
      BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295 := by
    rw [BitVec.add_assoc, hconst]
  rw [hassoc, stage2NoEventSub32_one (by rw [hsp32]; omega), hsp32]
  rfl

/-- **The bracket pop's address is the push's**, `%stk + (%sp − 1)`. -/
theorem stage2NoEventWalkBracketPopAddr_eq (K : Stage2NoEventWalkCarry) {sp : Nat}
    (h1 : 1 ≤ sp) (h2 : sp < 2 ^ 32) :
    closeReadAddr K.stk (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat =
      K.stk + (sp - 1) := by
  unfold closeReadAddr
  have hsp32 : (BitVec.ofNat 32 sp).toNat = sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
  rw [stage2NoEventSub32_one (by rw [hsp32]; omega), hsp32]

/-! ### The frame byte

The push writes `natToBytes ((BitVec.ofNat 8 fr).toNat) 1`; reading it back is
`fr`, and it is one byte because `fr < 2^8`. -/

/-- **The pushed frame byte reads back as `fr`.** -/
theorem stage2NoEventWalkNatToBytes_one_toNat {fr : Nat} (h : fr < 2 ^ 8) :
    bytesToNat (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) = fr := by
  have hv : (BitVec.ofNat 8 fr).toNat < 256 ^ 1 := by
    have hp : (256 : Nat) ^ 1 = 256 := by decide
    rw [hp, BitVec.toNat_ofNat]
    have hlt := Nat.mod_lt fr (by decide : 0 < 2 ^ 8)
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    omega
  rw [bytesToNat_natToBytes hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **The pushed frame byte's length.** -/
theorem stage2NoEventWalkNatToBytes_one_length (fr : Nat) :
    (natToBytes ((BitVec.ofNat 8 fr).toNat) 1).length = 1 :=
  natToBytes_length ..

/-! ### The stack is outside the document and the entry stream

The push lands inside `%stk`'s 520-byte extent; the document and the entry stream
are ABI regions, so the push does not disturb either read.  `Inv.sep` is the one
separation surface. -/

/-- **The entry stream is at or above the stack, or below it.** -/
theorem Stage2NoEventWalkInv.stackEpOrder {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    K.stk + 520 ≤ K.ep ∨ K.ep + 4 * K.nep ≤ K.stk := by
  have hd := disjointRegions_against
    (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
      K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
    (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep
    (a := K.ep) (n := 4 * K.nep) (by simp [stage2NoEventRegions])
    (r := (K.stk, stage2NoEventStackExtent)) (by simp [stage2NoEventStagedRegions])
  simpa [stage2NoEventStackExtent] using hd

/-- **The document is at or above the stack, or below it.** -/
theorem Stage2NoEventWalkInv.stackDocOrder {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    K.stk + 520 ≤ K.b ∨ K.b + (K.n + stage2ReadTail) ≤ K.stk := by
  have hd := disjointRegions_against
    (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
      K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
    (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep
    (a := K.b) (n := K.n + stage2ReadTail) (by simp [stage2NoEventRegions])
    (r := (K.stk, stage2NoEventStackExtent)) (by simp [stage2NoEventStagedRegions])
  simpa [stage2NoEventStackExtent] using hd

/-! ### The two guards

The facts the head does not carry, each one a route's branch guard.  The memory
reads, the closer's entry and the index bounds are *not* here: the producers
below derive them.

A guard states the branch that owns it, not an arithmetic consequence of being at
a head.  The seed's head has depth and frame zero (`Seed`'s
`loopHeadPhiCellsAt K 0 0 0 0 520`), so `1 ≤ sp` and `1 ≤ fr` are false there and
must not be head-level claims; the branch names them by exclusion (`sp ≠ 0`,
`fr ≠ 0`), and the committed rows' arithmetic positivity follows on `Nat`.  Which
branch a head is on is the assembly's case: a depth-zero head is the terminal
lane's (`JsonStage2NoEventWalkRowsContainerZero`), and only a non-zero depth
reaches these routes. -/

/-- **The pair routes' shared branch facts.**  Both container routes push one
frame byte and pop it back; the facts here are the push branch's. -/
structure Stage2NoEventWalkPairBranch (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop where
  /-- The push's stack guard: a non-zero depth.  At `sp = 0` the push at
  `if.then47.peel` (bracket) or `if.then20` (brace) is bypassed, so this row's
  stack staging is false at that head; the terminal lane is reached later, at
  `after_value`'s `%cmp355 = icmp eq %sp.4, 0`. -/
  spNe : ∀ sp, lookupName s.env "%sp.0.ph1403" =
    some (.int 32 (BitVec.ofNat 32 sp)) → sp ≠ 0
  /-- The push's stack room (`%exitcond.peel`'s bracket test, `%cmp10`'s brace
  test): the route continues only below the stack's 520 bytes. -/
  spLe : ∀ sp, lookupName s.env "%sp.0.ph1403" =
    some (.int 32 (BitVec.ofNat 32 sp)) → sp ≤ 519
  /-- The frame is non-zero on the pair branch, the frame-zero head being the
  depth-zero terminal lane's.  The route pushes `fr` and pops it back; the
  committed row also takes `1 ≤ fr`, which is this predicate's `Nat` form
  (`Nat.pos_of_ne_zero`), not an extra head-level claim. -/
  frNe : ∀ fr, lookupName s.env "%frame.0.ph1402" =
    some (.int 8 (BitVec.ofNat 8 fr)) → fr ≠ 0
  /-- The separator the shared cycle reads at the endpoint. -/
  comma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44
  /-- The next head exists. -/
  live : k + 3 < K.nep

/-- **The bracket pair's remaining premises at a head.**  The shared branch
facts and the closer's byte: the entry after the opener is `]`. -/
structure Stage2NoEventWalkBracketGuard (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop where
  /-- The pair routes' shared branch facts. -/
  branch : Stage2NoEventWalkPairBranch K k s
  /-- The entry after the opener is the closer `]`. -/
  closer : ∀ next nextByte, K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte → nextByte.toNat = 93

/-- **The brace pair's remaining premises at a head.**  The shared branch facts
and the closer's byte: the entry after the opener is `}`. -/
structure Stage2NoEventWalkBraceGuard (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop where
  /-- The pair routes' shared branch facts. -/
  branch : Stage2NoEventWalkPairBranch K k s
  /-- The entry after the opener is the closer `}`. -/
  closer : ∀ next nextByte, K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte → nextByte.toNat = 125

/-! ### The bracket class's producer

The class predicate supplies the opener's lane, byte and value; the guard the
four branch facts; everything else is derived here. -/

/-- **The empty array's row at a head.**  Beyond the class predicate and the
guard, every argument of `stage2NoEventWalkRow_cont_bracketPair` is a consequence
of `Head`: the closer's entry and byte, the post-push entry read and its width,
the document's byte at the closer, and the pop read of the pushed frame byte. -/
noncomputable def stage2NoEventWalkBracketRow_of_head {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hg : Stage2NoEventWalkBracketGuard K k s) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  -- the next head exists, so the pair's two entries do
  have hlt : k + 3 < K.nep := hg.branch.live
  have hkbound : k + 2 ≤ K.nep := by omega
  obtain ⟨next, nextByte, hk1, hbs1⟩ := h.closerEntry hkbound
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hb1 : nextByte.toNat = 93 := hg.closer next nextByte hk1 hbs1
  -- the head's stack cells and their widths
  obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
  have hspPos : 1 ≤ sp := by have := hg.branch.spNe sp hspH; omega
  have hspLe : sp ≤ 519 := hg.branch.spLe sp hspH
  have hfrPos : 1 ≤ fr := by have := hg.branch.frNe fr hfrH; omega
  -- the push's and the pop's one address
  have hpush : bracketPushAddr K (BitVec.ofNat 64 sp) = K.stk + (sp - 1) :=
    stage2NoEventWalkBracketPushAddr_eq K hspPos hspLt
  have hpop : closeReadAddr K.stk
      (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat = K.stk + (sp - 1) :=
    stage2NoEventWalkBracketPopAddr_eq K hspPos hspLt
  -- the separation's two orders
  have hepOrd := h.inv.stackEpOrder
  have hdocOrd := h.inv.stackDocOrder
  -- the entry stream's word at the closer's index
  have hk1lt : k + 1 < K.nep := by omega
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep) (n := K.nep)
    (l := K.ent) h.inv.entriesAt
  obtain ⟨q, bs4, hq, hread4, hval4q⟩ := hget (k + 1) hk1lt
  have hqnext : q = next := by
    rw [hq] at hk1
    exact Option.some.inj hk1
  have hval4 : bytesToNat bs4 = next := by rw [hval4q, hqnext]
  have hk1toNat : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by
      have := h.inv.nepLt; omega)
  -- the post-push entry read
  have hlaneW : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4 := by
    rw [hpush,
      show K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4 = K.ep + 4 * (k + 1) from by
        rw [hk1toNat]; omega]
    refine (readBytes_writeBytes_frame s.mem (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
      (K.stk + (sp - 1)) (K.ep + 4 * (k + 1)) 4 ?_).trans hread4
    rcases hepOrd with hord | hord
    · right
      rw [stage2NoEventWalkNatToBytes_one_length]
      omega
    · left; omega
  have hval4lt : bytesToNat bs4 < 2 ^ 32 := by
    rw [hval4]
    have hmax := h.inv.maxDoc
    simp only [stage2MaxDocument] at hmax
    omega
  -- the document's byte at the closer
  have hnext64 : (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat = next := by
    rw [hval4, stage2NoEventSignExtend_toNat (by omega : next < 2 ^ 64)]
  have hbyte1W : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte] := by
    rw [hnext64, hpush]
    have hgd : K.bs.getD next 0 = nextByte := by
      rw [List.getD_eq_getElem?_getD, hbs1]; rfl
    have hreadDoc : readBytes s.mem (K.b + next) 1 = some [nextByte] := by
      have hbyte := h.inv.docByte hnextLt
      rw [hgd] at hbyte
      simp [readBytes, hbyte]
    refine (readBytes_writeBytes_frame s.mem (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
      (K.stk + (sp - 1)) (K.b + next) 1 ?_).trans hreadDoc
    rcases hdocOrd with hord | hord
    · right
      rw [stage2NoEventWalkNatToBytes_one_length]
      omega
    · left; omega
  -- the pop reads the byte the push wrote
  have hbytePop : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1
      = some (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    rw [hpop, hpush]
    have hread := readBytes_writeBytes_same s.mem
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) (addr := K.stk + (sp - 1))
    rwa [stage2NoEventWalkNatToBytes_one_length] at hread
  have hbsLen : (natToBytes ((BitVec.ofNat 8 fr).toNat) 1).length = 1 :=
    stage2NoEventWalkNatToBytes_one_length fr
  have hbsVal : bytesToNat (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) = fr :=
    stage2NoEventWalkNatToBytes_one_toNat hfrLt
  -- the index's address bound
  have hk63 : k + 3 < 2 ^ 63 := by
    have h1 := h.inv.nepLe
    have h2 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  exact ⟨stage2NoEventWalkRow_cont_bracketPair (next := next) (nextByte := nextByte)
    (sp := sp) (fr := fr) (bs4 := bs4)
    (bs := natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
    h htrace hent hbs hb hk1 hbs1 hb1 hspH hfrH h1H hspPos hspLe hspLt hfrLt hfrPos
    hkbound hlaneW hval4lt hbyte1W hbytePop hbsLen hbsVal hg.branch.comma hlt hk63⟩

/-! ### The brace class's producer -/

/-- **The empty object's row at a head.**  The same derivation at the brace
class: no `%1` cell, the `{`/`}` pair, and `bracePushAddr`/`bracePopAddr`'s
32-bit depth arithmetic. -/
noncomputable def stage2NoEventWalkBraceRow_of_head {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBraceClass K k s)
    (hg : Stage2NoEventWalkBraceGuard K k s) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  have hlt : k + 3 < K.nep := hg.branch.live
  have hkbound : k + 2 ≤ K.nep := by omega
  obtain ⟨next, nextByte, hk1, hbs1⟩ := h.closerEntry hkbound
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hb1 : nextByte.toNat = 125 := hg.closer next nextByte hk1 hbs1
  obtain ⟨sp, fr, hspH, hfrH, -, hspLt, hfrLt⟩ := h.spPhiBounded
  have hspPos : 1 ≤ sp := by have := hg.branch.spNe sp hspH; omega
  have hspLe : sp ≤ 519 := hg.branch.spLe sp hspH
  have hfrPos : 1 ≤ fr := by have := hg.branch.frNe fr hfrH; omega
  have hpush : bracePushAddr K (BitVec.ofNat 32 sp) = K.stk + (sp - 1) :=
    stage2NoEventWalkBracePushAddr_eq K hspPos hspLt
  have hpop : bracePopAddr K sp = K.stk + (sp - 1) :=
    stage2NoEventWalkBracePopAddr_eq K hspPos hspLt
  have hepOrd := h.inv.stackEpOrder
  have hdocOrd := h.inv.stackDocOrder
  have hk1lt : k + 1 < K.nep := by omega
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep) (n := K.nep)
    (l := K.ent) h.inv.entriesAt
  obtain ⟨q, bs4, hq, hread4, hval4q⟩ := hget (k + 1) hk1lt
  have hqnext : q = next := by
    rw [hq] at hk1
    exact Option.some.inj hk1
  have hval4 : bytesToNat bs4 = next := by rw [hval4q, hqnext]
  have hk1toNat : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by
      have := h.inv.nepLt; omega)
  have hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4 := by
    rw [hpush,
      show K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4 = K.ep + 4 * (k + 1) from by
        rw [hk1toNat]; omega]
    refine (readBytes_writeBytes_frame s.mem (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
      (K.stk + (sp - 1)) (K.ep + 4 * (k + 1)) 4 ?_).trans hread4
    rcases hepOrd with hord | hord
    · right
      rw [stage2NoEventWalkNatToBytes_one_length]
      omega
    · left; omega
  have hval4lt : bytesToNat bs4 < 2 ^ 32 := by
    rw [hval4]
    have hmax := h.inv.maxDoc
    simp only [stage2MaxDocument] at hmax
    omega
  have hnext64 : (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat = next := by
    rw [hval4, stage2NoEventSignExtend_toNat (by omega : next < 2 ^ 64)]
  have hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte] := by
    rw [hnext64, hpush]
    have hgd : K.bs.getD next 0 = nextByte := by
      rw [List.getD_eq_getElem?_getD, hbs1]; rfl
    have hreadDoc : readBytes s.mem (K.b + next) 1 = some [nextByte] := by
      have hbyte := h.inv.docByte hnextLt
      rw [hgd] at hbyte
      simp [readBytes, hbyte]
    refine (readBytes_writeBytes_frame s.mem (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
      (K.stk + (sp - 1)) (K.b + next) 1 ?_).trans hreadDoc
    rcases hdocOrd with hord | hord
    · right
      rw [stage2NoEventWalkNatToBytes_one_length]
      omega
    · left; omega
  have hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)) (bracePopAddr K sp) 1
      = some (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    rw [hpop, hpush]
    have hread := readBytes_writeBytes_same s.mem
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) (addr := K.stk + (sp - 1))
    rwa [stage2NoEventWalkNatToBytes_one_length] at hread
  have hbsLen : (natToBytes ((BitVec.ofNat 8 fr).toNat) 1).length = 1 :=
    stage2NoEventWalkNatToBytes_one_length fr
  have hbsVal : bytesToNat (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) = fr :=
    stage2NoEventWalkNatToBytes_one_toNat hfrLt
  have hk63 : k + 3 < 2 ^ 63 := by
    have h1 := h.inv.nepLe
    have h2 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  exact ⟨stage2NoEventWalkRow_cont_bracePair (next := next) (nextByte := nextByte)
    (sp := sp) (fr := fr) (bs4 := bs4)
    (bs := natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
    h htrace hent hbs hb hk1 hbs1 hb1 hspH hfrH hspPos hspLe hspLt hfrLt hfrPos
    hkbound hlaneW hval4lt hbyte1W hbytePop hbsLen hbsVal hg.branch.comma hlt hk63⟩

/-! ### The producers at the assembly's predicates

`Stage2NoEventWalkBracketReady`/`…BraceReady` are the assembly's contracts.  They
follow from the two rows once each head is placed on one of the walk's two arms.

**The two arms.**  `after_value`'s `%cmp355 = icmp eq %sp.4, 0` splits the heads:
the live pair arm (`sp ≠ 0`, `k + 3 < K.nep`) takes the class row through
`…Row_of_head`, and the terminal arm (`sp = 0` or `k + 3 ≥ K.nep`) takes the
class's terminal row.  Each producer below states one premise per arm:

* `hpair` supplies, at a live head of the class, the shared
  `Stage2NoEventWalkPairBranch` beside the class's closer byte — that is, the
  class's `…Guard`.  It is satisfiable: a `[…]` head at positive depth whose next
  entry is the `]` closer is such a head, and both of its conjuncts are route
  facts, not the seed's.
* `hterm` supplies the terminal arm's row.  It is satisfiable at a nested pair:
  a seed head has `sp = 0`, so for a document opening with `[` (or `{`) it is a
  bracket (brace) head on this arm, and `stage2NoEventWalkBracketZeroRow`
  (`…BraceZeroRow`) produces the row there from the head, the endpoint's
  `after_value` cells and the caller's `hreportAcc`/`hboundAcc`/`hreportRef`.
  The other half of the arm — a trailing entry at non-zero depth
  (`K.nep ≤ k + 3` with `sp ≠ 0`) — is the same terminal route, but no producer
  for it is named in this tree yet; a caller on that half supplies its exit
  evidence itself.

Neither premise quantifies over *every* head: `hpair` is restricted to live
heads of the class and is refuted on the descend branch, `hterm` to the terminal
arm.  Nothing here claims either holds:
`hterm`'s row is the caller's terminal evidence, reachable only from the
endpoint's post words, and `hpair`'s branch facts are route predicates `Head`
does not carry.  `%xj = K.next0` is the invariant's (`Head.inv.xjNext0`), and
every memory read both rows take is derived in this module. -/

/-- **The bracket class's producer**, from the live pair arm's guard and the
terminal arm's row.  The head's depth is read at `%sp.0.ph1403`; a zero depth or
an index past the pair's next head is the terminal arm. -/
noncomputable def stage2NoEventWalkBracketReady_of_arms {calls : Calls} {mem : Mem}
    {F : Nat}
    (hpair : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      sp ≠ 0 → k + 3 < K.nep →
      Stage2NoEventWalkBracketGuard K k s)
    (hterm : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      (sp = 0 ∨ K.nep ≤ k + 3) →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkBracketReady calls mem F :=
  fun K k s h htrace hclass => by
    classical
    apply Classical.choice
    obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
    by_cases hsp0 : sp = 0
    · exact ⟨hterm K k s sp h htrace hclass hspH (Or.inl hsp0)⟩
    · by_cases hlive : k + 3 < K.nep
      · exact ⟨stage2NoEventWalkBracketRow_of_head h htrace hclass
          (hpair K k s sp h htrace hclass hspH hsp0 hlive)⟩
      · exact ⟨hterm K k s sp h htrace hclass hspH (Or.inr (by omega))⟩

/-- **The brace class's producer**, from the live pair arm's guard and the
terminal arm's row. -/
noncomputable def stage2NoEventWalkBraceReady_of_arms {calls : Calls} {mem : Mem}
    {F : Nat}
    (hpair : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      sp ≠ 0 → k + 3 < K.nep →
      Stage2NoEventWalkBraceGuard K k s)
    (hterm : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      (sp = 0 ∨ K.nep ≤ k + 3) →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkBraceReady calls mem F :=
  fun K k s h htrace hclass => by
    classical
    apply Classical.choice
    obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
    by_cases hsp0 : sp = 0
    · exact ⟨hterm K k s sp h htrace hclass hspH (Or.inl hsp0)⟩
    · by_cases hlive : k + 3 < K.nep
      · exact ⟨stage2NoEventWalkBraceRow_of_head h htrace hclass
          (hpair K k s sp h htrace hclass hspH hsp0 hlive)⟩
      · exact ⟨hterm K k s sp h htrace hclass hspH (Or.inr (by omega))⟩

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkHead.spPhiBounded
#print axioms Stage2NoEventWalkHead.closerEntry
#print axioms stage2NoEventWalkBracketRow_of_head
#print axioms stage2NoEventWalkBraceRow_of_head
#print axioms stage2NoEventWalkBracketReady_of_arms
#print axioms stage2NoEventWalkBraceReady_of_arms

end LeanLLVM.Refinement
