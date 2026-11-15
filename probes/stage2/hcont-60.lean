/-
# The 60-field `HcontFacts`: the verified-but-reverted shape

This file is a **record, not a build unit.**  It is the bundle surgery that was applied to
`JsonStage2WalkRevolution.lean`, elaborated module-green (`+JsonStage2WalkRevolution`,
`LAKE_EXIT=0`), and then reverted when the producer (`hcontFacts_of_staging`) and the
consumer (`walkRevolutionMergeSegWs`) rewrites were still unfinished — the producer had a
doc-comment syntax error and the consumer still read the deleted fields.  The reverted
bytes were not on disk; this file reconstructs them from the session so the proof survives.

**Two facts the attempt established.**
The class field necessarily conjoins the skip's per-index group, the non-emptiness, the inner budget and the price's `entryPos` start.
`b8` and `x1` were one word (the old `hRun` silently pinned them equal), so the arithmetic is 64 − 5 + 1 = **60**, not 61.

What was in the tree when it was green, in order: `wsPreS`/`wsSlS` (the total source and
stop terms), the three `wsPreS_*` reductions, the 60-field `structure HcontFacts` below,
the six `wsPreS_idx*`/`wsPreS_cond*` peels, `wsSlS_8`, `wsBit45`, `contWsRunF` and
`contWsPriceF`.  `contWsRun33/35/37`, `wsEntry33/35/37`, `wsFirstSeg43/46/48`,
`wsSeamSeg`, `wsStopAt_pre43/46/48`, `wsContAfterPre`, `wsPrice` and `wsRun` are already
landed in `JsonStage2WalkRevolution` (commit `10c523a`).

**What was left when it was reverted.**  In order:
1. `hcontFacts_of_staging`: drop the `{sl}`/`{b8}` binders and the `hRun`/`hnRun`/`hcond_sl`
   arguments, add `hClass`, restate `h8c`/`hTail`/`h3S`/`hreadS`/`hloc105`/`h47`/`hloc96`/
   `hlatch` at `contWsSlStaging G C s v ix b35 k` (an abbrev of `wsSlS` at the staging's
   values), and fill the literal with `k`, `n`, `hClass`, `x1 := hlastByte G C`.
2. `walkRevolutionMergeSegWs` (and `walkMergeCells_ws`, `walkDispatch_at_continue_cells_ws`):
   take `hk : C.k + 1 < G.nep`, replace `f.sl` by `wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix
   f.b35 f.k`, replace `f.hRun` by `obtain ⟨N, hN, hsegRun, hcond⟩ := contWsRunF G C s f
   hseg8.inv' hk`, replace `f.n` by `N`, and `f.hnRun` by `contWsPriceF G C s f hN`.
   `f.b8` becomes `f.x1`.
3. The `#print axioms` list gains the new declarations.

`n` is retained as a field (the decision kept it) although the derived segment's count is
the existential `N`; it is the one field the derivation does not read, so `59` is available
if the count is ever revisited.
-/

import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The total source and stop terms -/

/-- **The preheader state `%35`'s class selects, as a total function.**  The bundle names
the run's source without carrying the class as data: the branches on the byte's pivot bits
are the three arms, and under the class premise the branch taken *is* the arm's state
(`wsPreS_33/35/37`). -/
def wsPreS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
    leafBlock33OutAt (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
      (cont35 b35)
  else if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
    leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35)
  else
    leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35)

/-- **The stop state the skip reaches from that source**, as a total function of the
bundle's own values.  Under the class premise it is the arm's endpoint, so the fields the
run's endpoint names (`h8c`, `hTail`, the landing) are stated at it. -/
def wsSlS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (k : Nat) : State :=
  wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (wsPreS G C s x inc nep ep v ix b35))
    ix.toNat) ix.toNat v.toNat k

/-- `wsPreS` at `LeafBlock33`'s class is that arm's preheader state. -/
theorem wsPreS_33 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1) :
    wsPreS G C s x inc nep ep v ix b35 =
      leafBlock33OutAt (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
        (cont35 b35) := by
  rw [wsPreS, if_pos hb13]

/-- `wsPreS` at `LeafBlock35`'s class is that arm's preheader state. -/
theorem wsPreS_35 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1) :
    wsPreS G C s x inc nep ep v ix b35 =
      leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35) := by
  rw [wsPreS, if_neg (by rw [hb13]; decide), if_pos hb32]

/-- `wsPreS` at `LeafBlock37`'s class is that arm's preheader state. -/
theorem wsPreS_37 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0) :
    wsPreS G C s x inc nep ep v ix b35 =
      leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35) := by
  rw [wsPreS, if_neg (by rw [hb13]; decide), if_neg (by rw [hb32]; decide)]

/-! ### The bundle, 60 fields

The committed bundle is 64.  This one retires `sl`, `hRun`, `hnRun`, `hcond_sl` and `b8`,
and adds `hClass`: 64 − 5 + 1 = 60.  The run is derived by `contWsRunF`; the price by
`contWsPriceF`; `sl` is the term `wsSlS`; `hcond_sl` is `contWsRunF`'s third conjunct; `b8`
is `x1` (the seam's byte, which the old `hRun` pinned to `%8` at its endpoint). -/
structure HcontFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0
  hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0
  hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0
  /-- The entry's index and the stream's count, and the count test's value.  `hnext` is
  `1` — a continuing entry has one after it — and it is the field that used to be `hge`
  with `= 0`: see this module's header for the arithmetic that made that uninhabited. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- **The next entry's position lane**: the table's pointer, the load's word, and the
  read.  `cond.true345.i` is three instructions — `gep`, `load i32`, `zext` — and this is
  what its step consumes. -/
  ep : Nat
  v : BitVec 32
  h5 : lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (contAS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The default arm's remaining cells, at the state `cond.true345.i` leaves. -/
  ix : BitVec 64
  hidx5 : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (contAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  /-- **The entry is not empty.**  `%cond350.i` is the next entry's position, above this
  entry's own index, so `cond.end349.i` takes `land.lhs.true357.i`.

  **Arm-specific:** the last entry's bundle carries the opposite value, because its
  `%cond350.i` is `%4` and the last entry ends the stream.  Two bundles can share a field
  name and correctly carry opposite values. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The byte before the entry's end**, which the whitespace check reads: its address is
  `%cond350.i - 1` and the document supplies the byte.  Its class is `hClass`'s first
  conjunct. -/
  b35 : UInt8
  hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  /-- **The whitespace skip's stop, its byte and its document group.**  `k` is the run's
  stop (which the token-end `phi` selects) and `x1` the head's byte at the seam.

  `hClass` is **the one supplied field that makes the run's segment total at this state**:
  `%35` is one of the four whitespace bytes, so the leaf the three pivots reach takes its
  *true* arm and the walk enters the skip; every byte the skip reads continues the token
  until `k`, which stops it.  Without it a total producer could not build the segment at
  the other classes — this bundle would be inhabited only by the whitespace arm.  The run
  itself is no longer a field: `contWsRunF` derives it from this class and the composition
  (`contWsRun33/35/37`), at a count of at most `5·(k - ix.toNat) + 10`, with the stop's
  `%cond350.i` cell beside it, and `contWsPriceF` derives the price from that count and the
  span's two ends.

  The group is stated in the bundle's own vocabulary: the class bits are on `cont35 b35`;
  the skip's are on `wsX G` at the index the latch carries (`ix.toNat`), and they reach
  `ix.toNat` itself because the first visit reads the entry's own first byte; `k` is the
  stop.  The group's last conjuncts are the inner budget the first visit's `ScanEntered`
  witness needs and the `entryPos` fact the price's `+5` rests on. -/
  k : Nat
  n : Nat
  x1 : BitVec 8
  hClass :
    ((evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)) ∧
    (∀ q, ix.toNat ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧ ix.toNat < k ∧
    v.toNat - ix.toNat ≤ C.inner ∧ entryPos G C.k ≤ ix.toNat
  /-- The run's stop is inside the entry, which is what makes the extra-token span
  `[k, v.toNat)` non-empty.  **This is the field the other class cannot carry**: on the
  scan-free arm the token's end is the entry's end, so `k` would be `v.toNat`. -/
  heicd : k < v.toNat
  /-- The entry's first byte's class, read at the seam's name. -/
  h8c : evalOperand (contWsSeamS C (wsSlS G C s x inc nep ep v ix b35 k) k x1)
    (.reg "%8") = some (.int 8 x1)
  hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0
  /-- The tail's own: its three call outcomes, the event it emits, the seed's words and
  its segment from the class-C span's target to `contWsEntry` — `consumerTailSegAt` at
  count `3`, its first index the run's stop `k` and its bound the lane's word.  The scan's
  entry `phi` is `%ee.1.i` on `if.then447.i`'s edge, and the seam fixed that cell at
  `ofNat 64 k` (`contWsEntry_ee`), which is why `hopS` is a theorem here and not a field. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
    (contWsTailStart C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1)
    (TailCarryScan (ContTailStartC C) ev)
    (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA) 3
  /-- The scan's landing: the byte's address and the byte.  The index is `k` — the seam's
  stored end — everywhere the landing's states name it. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
    cA rdv xA).env "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
    (landRhs457OutAt (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
      cA rdv xA) (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
      cA rdv xA) (BitVec.ofNat 64 k) a q)
    (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
    (ScanS₉₆ (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
      cA rdv xA) (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (contWsLatch C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA
      (BitVec.ofNat 64 k) a q x47)
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and the run's stop at or after this one's — the two facts that make
  the visits and the run no more than the span, and the price's byte term. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ k
  /-- **The traversal's round**: `walkScanRounds457`'s `hround`, unweakened — a visit at
  the byte the landing loads, at the counter's own index and the lane's bound. -/
  hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
    (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    p + 1 < v.toNat → p + 1 < 2 ^ 63 →
    lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
      "land.rhs457.i").env "%3" = some (.ptr a) →
    readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
    evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
      "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
    evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
    evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
    WalkLocal (ScanC₁₀₅ (ScanCLand C'))
      (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) →
    WalkLocal (ScanC₉₆ (ScanCLand C'))
      (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    WalkLocal { ScanCLand C' with block := "while.body462.i" }
      (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
      WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  /-- **The latch's guard**: `walkScanRounds457`'s `hguard`, unweakened. -/
  hguard : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ScanGuard s' "%q.0.i246" "%cond350.i" C'.inner
  /-- **The input's totality at every index the scan visits**: `walkScanRounds457`'s
  `hbyte`, unweakened — the model branches on a byte it does not store. -/
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
    C'.block = "while.body462.i" → p + 1 < v.toNat →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i").env "%3" = some (.ptr a) ∧
      readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) ∧
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x)
  /-- **The token record's register at the scan's exit.**  Stated over the states the
  traversal's counters pin, because `walkScanRounds457` returns its final state
  existentially; every block on the path binds its own cells and none rebinds `%t352.i`,
  so the fact is true of the model and the shape is the traversal's.

  **Supplied, not derived, and the reason is structural:** a traversal whose final state is
  existential has no named term to state a register at, and the layer has no preservation
  lemma for registers — the same shape as `happ₂` in `HlastFacts`, one level out. -/
  htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok)

/-! ### The preheader cells at each arm -/

theorem wsPreS_idx33 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (h : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (leafBlock33OutAt
      (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
  simp only [leafBlock33OutAt, nodeBlock41OutAt, contLandS, contEndS, condEnd349OutAt,
    cte345OutAt, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem wsPreS_idx35 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (h : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35)).env
      "%idxprom.i" = some (.int 64 ix) := by
  simp only [leafBlock35OutAt, contP39S, contP41S, contLandS, contEndS, condEnd349OutAt,
    cte345OutAt, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem wsPreS_idx37 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (h : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35)).env
      "%idxprom.i" = some (.int 64 ix) := by
  simp only [leafBlock37OutAt, contP37S, contP41S, contLandS, contEndS, condEnd349OutAt,
    cte345OutAt, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem wsPreS_cond33 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (leafBlock33OutAt
      (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
      (cont35 b35)).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [leafBlock33OutAt, nodeBlock41OutAt, contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact contEndS_cond C s x inc nep ep v ix

theorem wsPreS_cond35 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35)).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [leafBlock35OutAt, contP39S, contP41S, contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact contEndS_cond C s x inc nep ep v ix

theorem wsPreS_cond37 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35)).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [leafBlock37OutAt, contP37S, contP41S, contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact contEndS_cond C s x inc nep ep v ix

/-- `%8` at the seam is the byte the seam tests: the seam binds five cells none of which is
`%8`, so the cell is the state's. -/
theorem wsSlS_8 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (k : Nat) (x1 : BitVec 8)
    (h : evalOperand (contWsSeamS C (wsSlS G C s x inc nep ep v ix b35 k) k x1)
      (.reg "%8") = some (.int 8 x1)) :
    lookupName (wsSlS G C s x inc nep ep v ix b35 k).env "%8" =
      some (.int 8 x1) := by
  simp only [contWsSeamS, seamS, seamFin, stateAt, evalOperand] at h
  repeat rw [lookupName_cons_ne _ _ (by decide)] at h
  exact h

/-- `%8`'s test at the seam is clear when the byte is at or above `110`: the `45` branch and
the `[48, 58)` window are both below it.  `slt` on bytes is signed, and the hypothesis rules
out the `[128, 256)` half, so the byte is in `[110, 128)`. -/
theorem wsBit45 {x : BitVec 8}
    (h : evalICmp .slt x (BitVec.ofNat 8 110) = 0) :
    (evalICmp .eq x (BitVec.ofNat 8 45) ||| evalICmp .ult (x + BitVec.ofNat 8 208)
      (BitVec.ofNat 8 10)) = 0 := by
  simp only [evalICmp] at h ⊢
  bv_decide

/-- **The run's segment, from the bundle's class field.**  The three arms of `%35`'s class
give the source; `contWsRun33/35/37` gives the segment, its count bound and the stop's
`%cond350.i` cell. -/
theorem contWsRunF {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s)
    (hInv₈ : WalkInv G (ContAC₄ C) (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35))
    (hk : C.k + 1 < G.nep) :
    ∃ N, N ≤ 5 * (f.k - f.ix.toNat) + 10 ∧
      WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C)
        (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (ContSeamC C)
        (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1) N ∧
      lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := by
  obtain ⟨hcase, hcls, hstop, hik, hvsub, hstartI⟩ := f.hClass
  have hiv : f.ix.toNat < f.v.toNat := by
    have h := (evalICmp_ugt_one_iff_toNat (BitVec.ofNat 64 f.v.toNat) f.ix).1 f.hugt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := f.v.isLt; omega)] at h
    exact h
  have hcw : f.v.toNat < 2 ^ 64 := by have := f.v.isLt; omega
  have hposE : entryPos G (C.k + 1) < G.n := entryPos_lt G hk
  have hgn : f.ix.toNat < G.n := by have := f.hspan; omega
  have hi63 : f.ix.toNat < 2 ^ 63 := by
    have h1 := G.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hpos : ∀ q, f.ix.toNat < q → q ≤ f.k → q < 2 ^ 63 := by
    intro q h1 h2
    have h1' := G.maxDoc
    simp only [stage2MaxDocument] at h1'
    have h3 : q ≤ f.k := h2
    have h4 : f.k < f.v.toNat := f.heicd
    have h5 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have h6 := hposE
    have h7 : q < G.n := by omega
    omega
  have hqn : ∀ q, f.ix.toNat < q → q ≤ f.k → q < G.n := by
    intro q h1 h2
    have h4 : f.k < f.v.toNat := f.heicd
    have h5 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    omega
  have halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve := by
    have h := hInv₈.alen_le
    change C.alen ≤ G.ndst0 + G.n at h
    omega
  have hevlen : C.evlen ≤ G.evcap := by
    have h1 := hInv₈.evlen_le
    change C.evlen ≤ G.nev0 + stage2RecordBytes * G.n at h1
    have h2 := G.evRoom
    omega
  have hcontI : wsCont G f.ix.toNat := hcls f.ix.toNat le_rfl hik
  have hcls' : ∀ q, f.ix.toNat < q → q < f.k → wsCont G q :=
    fun q h1 h2 => hcls q (by omega) h2
  have hbitsl : (evalICmp .eq f.x1 (BitVec.ofNat 8 45) |||
      evalICmp .ult (f.x1 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 :=
    wsBit45 f.hc110
  have h8sl : lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env "%8" =
      some (.int 8 f.x1) :=
    wsSlS_8 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k f.x1 f.h8c
  rcases hcase with ⟨hb13, hws⟩ | ⟨hb13, hb32, hbq13⟩ | ⟨hb13, hb32, hbq32⟩
  · have hpre := wsPreS_33 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 hb13
    have hidx := wsPreS_idx33 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.hidx5
    have hcond := wsPreS_cond33 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35
    have h8sl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (cont35 f.b35))
        (cont35 f.b35))) f.ix.toNat) f.ix.toNat f.v.toNat f.k).env "%8" =
        some (.int 8 f.x1) := by
      simpa only [wsSlS, hpre] using h8sl
    simpa only [wsSlS, hpre] using
      (contWsRun33 (calls := stage2Calls stage2SubCalls) G C s f.x f.inc f.nep f.ep f.v f.ix
        f.b35 hInv₈ hb13 hws hidx hcond hiv hvsub hcw hi63 hgn hik f.heicd hcontI hcls'
        hstop hpos hqn halen hevlen h8sl' hbitsl)
  · have hpre := wsPreS_35 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 hb13 hb32
    have hidx := wsPreS_idx35 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.hidx5
    have hcond := wsPreS_cond35 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35
    have h8sl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (contP39S C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (cont35 f.b35))) f.ix.toNat)
        f.ix.toNat f.v.toNat f.k).env "%8" = some (.int 8 f.x1) := by
      simpa only [wsSlS, hpre] using h8sl
    simpa only [wsSlS, hpre] using
      (contWsRun35 (calls := stage2Calls stage2SubCalls) G C s f.x f.inc f.nep f.ep f.v f.ix
        f.b35 hInv₈ hb13 hb32 hbq13 hidx hcond hiv hvsub hcw hi63 hgn hik f.heicd hcontI hcls'
        hstop hpos hqn halen hevlen h8sl' hbitsl)
  · have hpre := wsPreS_37 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 hb13 hb32
    have hidx := wsPreS_idx37 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.hidx5
    have hcond := wsPreS_cond37 G C s f.x f.inc f.nep f.ep f.v f.ix f.b35
    have h8sl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (contP37S C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (cont35 f.b35))) f.ix.toNat)
        f.ix.toNat f.v.toNat f.k).env "%8" = some (.int 8 f.x1) := by
      simpa only [wsSlS, hpre] using h8sl
    simpa only [wsSlS, hpre] using
      (contWsRun37 (calls := stage2Calls stage2SubCalls) G C s f.x f.inc f.nep f.ep f.v f.ix
        f.b35 hInv₈ hb13 hb32 hbq32 hidx hcond hiv hvsub hcw hi63 hgn hik f.heicd hcontI hcls'
        hstop hpos hqn halen hevlen h8sl' hbitsl)

/-- **The run's price, from the bundle.**  `wsPrice` at the class field's start fact and the
span's end. -/
theorem contWsPriceF {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s) {N : Nat} (hN : N ≤ 5 * (f.k - f.ix.toNat) + 10) :
    N + stage2ByteAllowance * (f.v.toNat - 1 - f.k) ≤
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5 :=
  wsPrice hN f.hClass.2.2.2.1 f.heicd f.hClass.2.2.2.2.2 f.hspan

/-! ### The producer's stop-term abbrev (the rewrite that was started) -/

/-- The bundle's stop term at the staging's own values: the total function of `b35`, the
lane's word and the run's stop. -/
abbrev contWsSlStaging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) (k : Nat) : State :=
  wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35 k

end WalkScope
end LeanLLVM.Refinement
