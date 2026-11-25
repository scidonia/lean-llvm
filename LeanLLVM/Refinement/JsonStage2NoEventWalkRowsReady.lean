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

**The three arms.**  The split is room first, byte second: a head with no room
at `k + 2` for the pair's own liveness (`K.nep ≤ k + 3`) is the trailing exit
whatever its bytes, and only a head with room reads the byte at `k + 1`, where
`if.end327.peel` tests it against `]` and sends the walk to the closer route
while its failure continues through `if.end` into the next element (the
descend).  The rows this tree has are the
**closer arm's**: the depth-zero route (`…BracketZeroRow`/`…BraceZeroRow`) and
the committed empty-pair cycle (`…BracketRow_of_head`/`…BraceRow_of_head`).  The
**descend arm is the missing route** — no term in this tree produces a row on
`if.end` — and it is the branch the walk takes at `[[`'s inner `[`; an earlier
form of this module required the closer's byte at every live head of the class
and was refuted exactly there.

**What the descend arm would need, and why it is not derived here.**  Its
staging is `Stage2NoEventWalkPairBranch`: the push's stack discipline
(`sp ≠ 0`, `sp ≤ 519`; `Head.layers` binds `sp < 2^32` only, and
`Inv.stagedBytes` gives the stack's extent, not a bound on the register), the
frame (`fr ≠ 0`), the separator at `k + 2` (`Inv.doc` gives the document byte's
*presence*, never its value) and the next head's liveness (`Head` carries
`k < K.nep` only).  Each is a route fact, not a head consequence: the seed head
has depth and frame zero (`Seed`'s `loopHeadPhiCellsAt K 0 0 0 0 520`), so
`1 ≤ sp` and `1 ≤ fr` are false there, and `sp ≠ 0`/`fr ≠ 0` name the branch by
exclusion (`Nat.pos_of_ne_zero` is the committed rows' arithmetic form).  The
producers below therefore take the descend row as a byte-restricted premise and
leave its staging to the route's own proof.

The closer's byte is a separate class of fact, `Stage2NoEventWalkBracketCloser`/
`…BraceCloser` — the closer arm's test (`%cmp332.peel`), not the descend staging.
The trailing exit's `Stage2NoEventWalkExit` evidence (`Stage2NoEventRun` report
and `stage2NoEventBoundary`) is the caller's post, carried by neither `Head` nor
`Trace`.  The carry's `%xj = K.next0` is **not** an arm's premise: it is the
invariant's static equality (`Stage2NoEventWalkInv.xjNext0`), projected at a head
as `Stage2NoEventWalkHead.xjNext0`.  Every memory read and index bound the
committed rows take is derived in this module.
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

/-! ### The descend arm's staging, and the closer's byte

The facts the head does not carry, each one a route's own.  The memory reads,
the entries and the index bounds are *not* here: the producers below derive them.

`Stage2NoEventWalkPairBranch` is the **descend arm's** staging — the branch
`if.end327.peel`'s false byte test reaches (`if.end`), where the walk pushes a
frame and moves to the next element.  It states the branch's own facts, not an
arithmetic consequence of being at a head: the seed's head has depth and frame
zero (`Seed`'s `loopHeadPhiCellsAt K 0 0 0 0 520`), so `1 ≤ sp` and `1 ≤ fr` are
false there, and the branch names them by exclusion (`sp ≠ 0`, `fr ≠ 0`) with
the committed rows' arithmetic positivity as the `Nat` consequence.

The closer's byte is **not** part of that staging: it is the closer arm's own
test (`if.end327.peel`'s `%cmp332.peel`), stated as
`Stage2NoEventWalkBracketCloser`/`…BraceCloser`.  The descend arm is the missing
route — no term in this tree produces a row on the `if.end` branch — so the
producers below take it as a byte-restricted route premise. -/

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

/-- **The closer arm's byte, for the `[]` pair.**  The entry after the opener is
the closer `]`: `if.end327.peel`'s `%cmp332.peel` test. -/
def Stage2NoEventWalkBracketCloser (K : Stage2NoEventWalkCarry) (k : Nat) : Prop :=
  ∀ next nextByte, K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte → nextByte.toNat = 93

/-- **The closer arm's byte, for the `{}` pair.**  The entry after the opener is
the closer `}`: `if.end303`'s test. -/
def Stage2NoEventWalkBraceCloser (K : Stage2NoEventWalkCarry) (k : Nat) : Prop :=
  ∀ next nextByte, K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte → nextByte.toNat = 125

/-! ### The bracket class's closer-arm producer

The class predicate supplies the opener's lane, byte and value; the pair branch
the descend arm's staging facts and the closer predicate the byte test;
everything else is derived here.  This is the row the closer arm's premise is
inhabited with when the depth is non-zero (the committed empty-pair cycle); the
depth-zero case is `…BracketZeroRow`. -/

/-- **The empty array's row at a head.**  Beyond the class predicate, the pair
branch and the closer's byte, every argument of
`stage2NoEventWalkRow_cont_bracketPair` is a consequence of `Head`: the closer's
entry, the post-push entry read and its width, the document's byte at the closer,
and the pop read of the pushed frame byte. -/
noncomputable def stage2NoEventWalkBracketRow_of_head {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hg : Stage2NoEventWalkPairBranch K k s)
    (hclose : Stage2NoEventWalkBracketCloser K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  -- the next head exists, so the pair's two entries do
  have hlt : k + 3 < K.nep := hg.live
  have hkbound : k + 2 ≤ K.nep := by omega
  obtain ⟨next, nextByte, hk1, hbs1⟩ := h.closerEntry hkbound
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hb1 : nextByte.toNat = 93 := hclose next nextByte hk1 hbs1
  -- the head's stack cells and their widths
  obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
  have hspPos : 1 ≤ sp := by have := hg.spNe sp hspH; omega
  have hspLe : sp ≤ 519 := hg.spLe sp hspH
  have hfrPos : 1 ≤ fr := by have := hg.frNe fr hfrH; omega
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
    hkbound hlaneW hval4lt hbyte1W hbytePop hbsLen hbsVal hg.comma hlt hk63⟩

/-! ### The brace class's producer -/

/-- **The empty object's row at a head.**  The same derivation at the brace
class: no `%1` cell, the `{`/`}` pair, and `bracePushAddr`/`bracePopAddr`'s
32-bit depth arithmetic. -/
noncomputable def stage2NoEventWalkBraceRow_of_head {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBraceClass K k s)
    (hg : Stage2NoEventWalkPairBranch K k s)
    (hclose : Stage2NoEventWalkBraceCloser K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  have hlt : k + 3 < K.nep := hg.live
  have hkbound : k + 2 ≤ K.nep := by omega
  obtain ⟨next, nextByte, hk1, hbs1⟩ := h.closerEntry hkbound
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hb1 : nextByte.toNat = 125 := hclose next nextByte hk1 hbs1
  obtain ⟨sp, fr, hspH, hfrH, -, hspLt, hfrLt⟩ := h.spPhiBounded
  have hspPos : 1 ≤ sp := by have := hg.spNe sp hspH; omega
  have hspLe : sp ≤ 519 := hg.spLe sp hspH
  have hfrPos : 1 ≤ fr := by have := hg.frNe fr hfrH; omega
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
    hkbound hlaneW hval4lt hbyte1W hbytePop hbsLen hbsVal hg.comma hlt hk63⟩

/-! ### The producers at the assembly's predicates

`Stage2NoEventWalkBracketReady`/`…BraceReady` are the assembly's contracts.  They
follow once every head of the class is placed on one of the three arms
`if.end327.peel` (or `if.end303` for the brace) selects:

**The three arms.**  The split is room first, byte second.  A head with no room
at `k + 2` for the pair's own liveness (`K.nep ≤ k + 3`) is the trailing exit,
whatever its bytes; only a head with room reads the byte at `k + 1`, where
`if.end327.peel` tests it against `]` (the closer) and, when the test fails,
`if.end` continues into the next element (the descend).  Each producer below
states one premise per arm:

* `hcloser` — room, and the closer byte at `k + 1`: the row is the closer
  route's.  At depth zero `stage2NoEventWalkBracketZeroRow` (`…BraceZeroRow`)
  produces it from the endpoint's `after_value` cells and the caller's
  `hreportAcc`/`hboundAcc`/`hreportRef`.  At positive depth the tree's producer,
  `…BracketRow_of_head` (`…BraceRow_of_head`), additionally needs
  `Stage2NoEventWalkPairBranch` — notably the separator at `k + 2`.  So the
  arm is inhabited in-tree only on the **comma-continuation** shape: an empty
  pair that is the *last element of its parent* has `K.ent[k + 2]` a bracket
  byte, the separator fails, and no producer here applies.  That shape is the
  **second missing route**, beside the descend one.
* `hdescend` — an entry at `k + 1` whose byte is not the closer: **the missing
  route**.  The tree has no producer for `if.end`; a caller supplies this row
  from the descend route — the push at `sp ≠ 0` (with `sp ≤ 519` and `fr ≠ 0`)
  and the cycle to the next element's head (`stage2NoEventWalkCycle_of_pair`'s
  shape at the class dispatch), the push skipped at `sp = 0` — and the route's
  own staging (`Stage2NoEventWalkPairBranch`, the separator at `k + 2`) is part
  of that proof, not a hypothesis of this definition.
* `htrail` — no room at `k + 2` (`K.nep ≤ k + 3`): the trailing exit, whose
  `Stage2NoEventWalkExit` evidence is the caller's post.  This arm takes every
  head at `nep = k + 3` as well as the shorter ones, matching the pair's own
  liveness `k + 3 < K.nep`.

The premises are restricted to the arm each names, so none is a claim about
*every* head; the old form that quantified over every live head of the class is
refuted by a descend head (`[[` opens and is not the closer).  Nothing here
claims an arm holds: `hdescend` and the parent-closer shape are exactly the
routes this tree lacks, and `%xj = K.next0` is the invariant's
(`Head.inv.xjNext0`), not an arm's premise. -/

/-- **The bracket class's producer**: the closer arm, the descend arm and the
trailing exit, each stated at the byte that selects it. -/
noncomputable def stage2NoEventWalkBracketReady_of_routes {calls : Calls} {mem : Mem}
    {F : Nat}
    (hcloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat)
        (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      Stage2NoEventWalkRow calls mem F K k s)
    (hdescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat)
        (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 93 →
      Stage2NoEventWalkRow calls mem F K k s)
    (htrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkBracketReady calls mem F :=
  fun K k s h htrace hclass => by
    classical
    apply Classical.choice
    obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
    by_cases hk2 : K.nep ≤ k + 3
    · exact ⟨htrail K k s sp h htrace hclass hspH hk2⟩
    · have hk2le : k + 2 ≤ K.nep := by omega
      obtain ⟨next, hk1⟩ := h.entSucc hk2le
      have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
      obtain ⟨nextByte, hbs1⟩ := h.inv.docGetElem? hnextLt
      by_cases hcl : nextByte.toNat = 93
      · exact ⟨hcloser K k s sp next nextByte h htrace hclass hspH hk1 hbs1 hcl⟩
      · exact ⟨hdescend K k s sp next nextByte h htrace hclass hspH hk1 hbs1 hcl⟩

/-- **The brace class's producer**: the closer arm, the descend arm and the
trailing exit, each stated at the byte that selects it. -/
noncomputable def stage2NoEventWalkBraceReady_of_routes {calls : Calls} {mem : Mem}
    {F : Nat}
    (hcloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat)
        (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 125 →
      Stage2NoEventWalkRow calls mem F K k s)
    (hdescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat)
        (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 125 →
      Stage2NoEventWalkRow calls mem F K k s)
    (htrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkBraceReady calls mem F :=
  fun K k s h htrace hclass => by
    classical
    apply Classical.choice
    obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
    by_cases hk2 : K.nep ≤ k + 3
    · exact ⟨htrail K k s sp h htrace hclass hspH hk2⟩
    · have hk2le : k + 2 ≤ K.nep := by omega
      obtain ⟨next, hk1⟩ := h.entSucc hk2le
      have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
      obtain ⟨nextByte, hbs1⟩ := h.inv.docGetElem? hnextLt
      by_cases hcl : nextByte.toNat = 125
      · exact ⟨hcloser K k s sp next nextByte h htrace hclass hspH hk1 hbs1 hcl⟩
      · exact ⟨hdescend K k s sp next nextByte h htrace hclass hspH hk1 hbs1 hcl⟩

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkHead.spPhiBounded
#print axioms Stage2NoEventWalkHead.closerEntry
#print axioms stage2NoEventWalkBracketRow_of_head
#print axioms stage2NoEventWalkBraceRow_of_head
#print axioms stage2NoEventWalkBracketReady_of_routes
#print axioms stage2NoEventWalkBraceReady_of_routes

end LeanLLVM.Refinement
