/-
The no-event walk's container class row: the empty pair's route to the
after-value endpoint, and the shared cycle's return to the next head.

A count class's continuing row is the same object at every class: a counted
route from the head to `after_value`'s entry, the shared cycle from there to the
next head, and one price for the composition.  This module states that object as
one general lemma, `stage2NoEventWalkRow_cont_of_afterValue`, and proves the
container class's route as its first instance.

* **the general row.**  The route is a `Stage2NoEventWalkSegment` at its own
  count, from the head to the class's endpoint; the endpoint is the class's
  `Stage2NoEventWalkCycleSrc` (the `after_value` entry, the class's carry and
  trace, the dispatch's `phi` run, and the carried base lookups); the return is
  the cycle `Stage2NoEventWalkCycle` at the endpoint's index.  The lemma composes
  the two segments, hands the cycle's `head'`/`trace'` to the row, and prices the
  route against the endpoint: the class supplies
  `j + Φ Kc kc ≤ Φ K k` for its own `j`, and the cycle's `8 + Φ Kc (kc+1) ≤ Φ Kc kc`
  is its own credit.  The three static numbers (`nep`, `a12`, `next0`) and the
  index growth are the route's facts; `k' < K.nep` is the cycle source's own
  liveness at the endpoint.

* **the container instance.**  An empty array's head is `[` at the head's lane and
  `]` at the next entry's lane.  The route is the body's own eleven blocks: the
  three-block dispatch to `if.then35.peel`, the four blocks of the bracket push to
  `if.end327.peel` (one stack byte stored), that block's `]` read to `if.then334`,
  the count store (`+2` events, `+7` terms), `close_arr`, and `if.then350`'s pop
  read, to `after_value` at index `k + 2`.  The cycle then returns to the head at
  `k + 3`, so the row advances three entries.

**The price.**  The row consumes the opener and the closer in the route and the
backedge's one entry in the cycle, so its credit is
`32·3 + 8·(ent[k+3] − ent[k])`, at least `96`.  The class leg is priced against
its own two-entry advance: `11 + Φ Kc (k+2) ≤ Φ K k` is `11 ≤ 64 + 8·Δ`, which the
eleven blocks satisfy with room.  It is *not* priced by
`stage2NoEventWalkContainerPairCredit`: that lemma is the potential's difference
over a one-entry advance, not the leg's count, and the row's composition never
needs it.  The cycle's eight are its own credit at `Φ Kc (k+3)`.

**The row as data.**  `Stage2NoEventWalkRow` is a `Type`, so a class row is built,
not proved.  The route and the cycle each name their target's state existentially:
the route's segment counts a run to a *given* endpoint, and
`stage2NoEventWalkCycle_of_afterValue` names the next head and the cycle's price.
Composing them therefore extracts those witnesses classically — the row's only
classical step.  The route's count and price, the endpoint's bundle, and the
cycle's segment and credit are the constructive facts above.

**What is not proved here.**  The route takes the memory reads its blocks perform
as staging (the post-push entry lane and document byte at the closer, and the
popped stack byte), exactly as `stage2NoEventWalkContainerPushBracket` takes the
live depth and the stack room.  The object-member pair (`{` then `"`) is the
`if.end303` path, whose cycle is `d = 4` and is stated separately; it is not this
module's route.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkContainers
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA
import LeanLLVM.Refinement.JsonStage2NoEventWalkPremises

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The general continuing row

A class's counted route to `after_value`'s entry plus the shared cycle is a
`Stage2NoEventWalkRow.cont`.  The route carries its own count and its own price
to the endpoint; the cycle carries its segment, its target's `Head` and `Trace`,
and its own credit. -/

/-- **A priced class route to the after-value endpoint, followed by the cycle,
is a continuing row.**

`hroute` is the class's counted route from the head to its endpoint, at price
`j`; `hend` is the endpoint's bundle; `hcyc` is the cycle from the endpoint's
index `kc` to the next head at `kc + 1`.  The class pays only its own route
(`hprice`, to the endpoint's index); the cycle's credit is the cycle's.  The
composed row's price is `j + p`, its target is `kc + 1`, and the target's
`Head`/`Trace` are the cycle's.  `hk'lt` is the endpoint's liveness, transported
to the source carry by `hnep`. -/
def stage2NoEventWalkRow_cont_of_afterValue {calls : Calls} {mem : Mem}
    {F : Nat} {K Kc : Stage2NoEventWalkCarry} {k kc : Nat} {s sE s' : State}
    {j p : Nat}
    (hroute : Stage2NoEventWalkSegment calls mem K s Kc sE j)
    (hend : Stage2NoEventWalkCycleSrc calls mem Kc kc sE)
    (hcyc : Stage2NoEventWalkCycle calls mem Kc kc sE 1 s' p)
    (hnep : Kc.nep = K.nep) (ha12 : Kc.a12 = K.a12) (hn0 : Kc.next0 = K.next0)
    (hlt : k < kc + 1)
    (hprice : j + stage2NoEventWalkPotential Kc kc ≤ stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have htail : Stage2NoEventWalkHeadSegment calls mem K k s Kc (kc + 1) s' (j + p) :=
    { seg := hroute.trans hcyc.headPriced.seg.seg
      head' := hcyc.headPriced.seg.head'
      trace' := hcyc.headPriced.seg.trace' }
  refine Stage2NoEventWalkRow.cont (F := F) Kc (kc + 1) s' (j + p)
    ⟨htail, ?_⟩ hnep ha12 hn0 hlt ?_
  · have hcycle := hcyc.headPriced.credit
    omega
  · rw [← hnep]
    exact hend.klt

/-! ### Words and bytes

The route's cells are `BitVec.ofNat` words and the pop reads back the stack byte
the push wrote; the identities below are what the `phi` selections and the Src's
`Nat`-indexed fields need.
-/

/-- **A sum of two `ofNat` words is the `ofNat` of the sum.** -/
theorem stage2NoEventWalkOfNat_add (w a b : Nat) :
    BitVec.ofNat w a + BitVec.ofNat w b = BitVec.ofNat w (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.add_mod]

/-- **A one-byte list's value.** -/
theorem stage2NoEventWalkBytesToNat_single (b : UInt8) : bytesToNat [b] = b.toNat := by
  simp [bytesToNat]

/-- **A one-byte read's value is a byte.** -/
theorem stage2NoEventWalkBytesToNat_lt {bs : List UInt8} (h : bs.length = 1) :
    bytesToNat bs < 2 ^ 8 := by
  have hlt := bytesToNat_lt bs
  rw [h] at hlt
  simpa using hlt

/-- **A `cells` lookup at a name the list binds**, from the list's membership. -/
theorem stage2NoEventWalkCells_some {cs : List (String × Value)} {env : Env}
    {n : String} {v : Value} (hm : (n, v) ∈ cs) (hnd : (cs.map (·.1)).Nodup) :
    lookupName (cells cs env) n = some v :=
  cells_lookup_of_mem cs env hm hnd

/-- **A `cells` lookup at a name the list does not bind** reads through to the
incoming environment. -/
theorem stage2NoEventWalkCells_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (p, w) :: cs, n, env, h => by
      have hp : p ≠ n := by
        intro hpn
        exact h (by subst hpn; simp)
      simp only [cells, lookupName_cons_ne w (cells cs env) hp]
      exact stage2NoEventWalkCells_notin cs n env
        (fun hc => h (List.mem_cons_of_mem _ hc))

/-! ### The empty array's route

`[` at the head's lane and `]` at the next: the three-block dispatch, the
bracket's four push blocks (a live depth stores the frame byte at
`%stk + (%sp − 1)`), `if.end327.peel`'s `]` read, the count store, the depth test
and the pop read, to `after_value`'s entry.
-/

/-- **The empty array's route**, eleven blocks from the head to `after_value`'s
entry, with the pair's carry and the endpoint's `Stage2NoEventWalkCycleSrc`. -/
theorem stage2NoEventWalkBracketPairLeg {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (h1H : lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrLt : fr < 2 ^ 8) (hfrPos : 1 ≤ fr)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    ∃ (s' : State) (Kc : Stage2NoEventWalkCarry),
      Kc = { K with tok := K.tok + 2, terms := K.terms + 7 } ∧
      Stage2NoEventWalkSegment calls mem K s Kc s' 11 ∧
      Nonempty (Stage2NoEventWalkCycleSrc calls mem Kc (k + 2) s') := by
  classical
  let Kc : Stage2NoEventWalkCarry :=
    { K with tok := K.tok + 2, terms := K.terms + 7 }
  -- the head's own cells
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    h.bracketCell hk hbs hb
  have hstk : lookupName s.env "%stk" = some (.ptr K.stk) := h.stk
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := h.nepI
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) := h.epPtr
  have hbPtr : lookupName s.env "%b" = some (.ptr K.b) := h.bPtr
  have hincH : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
    exact hinc
  -- the values the route's cells carry
  have hkincLt : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
    omega
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt h.inv.nepLt]
    omega
  -- the eleven blocks
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 1) :: S1.env) S1 "LeafBlock1"
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 1) :: S2.env) S2
    "if.then35.peel"
  let S4 := stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: S3.env) S3
    "if.end45.peel"
  let S5 := stage2NoEventWalkNext (("%tobool46.not.peel", .int 1 0) :: S4.env) S4
    "if.then47.peel"
  let S6 := stage2NoEventWalkStored
    (("%arrayidx50.peel", .ptr (bracketPushAddr K (BitVec.ofNat 64 sp))) ::
      ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)) ::
      S5.env)
    S5 (writeBytes S5.mem (bracketPushAddr K (BitVec.ofNat 64 sp)) (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
    "if.end51.peel"
  let S7 := stage2NoEventWalkNext (("%cmp319.not.peel", .int 1 1) :: S6.env) S6
    "if.end327.peel"
  let S8 := stage2NoEventWalkNext
    (("%cmp332.peel", .int 1 1) ::
      ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) ::
      ("%arrayidx330.peel",
        .ptr (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4)) ::
      S7.env) S7 "if.then334"
  let S9 := stage2NoEventWalkNext
    (cells (ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
      (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)) S8.env) S8 "close_arr"
  let S10 := stage2NoEventWalkNext
    (cells (closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
      (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
      (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) S9.env) S9 "if.then350"
  -- `if.then350`'s pop: the frame byte at `%stk + (%sp - 1)`, one byte, read at the
  -- address the block computes (`closeReadAddr`), not the push's sign-extended one
  let popCells : List (String × Value) :=
    ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells50 (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) ++
      closeIdxCells50 (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295)
  let S11 := stage2NoEventWalkNext (cells popCells S10.env) S10 "after_value"
  -- the links
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h.inv h.pc h3 (by decide)
  have h3a : lookupName (("%Pivot6", .int 1 0) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_true L1.inv' rfl
      h3a (by decide)
  have h3b : lookupName (("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env)
      "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3a
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock1_true L2.inv' rfl
      h3b (by decide)
  have hspLe32 : (BitVec.ofNat 32 sp).toNat ≤ 519 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
    exact hspLe
  have hspNe32 : (BitVec.ofNat 32 sp).toNat ≠ 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
    omega
  have hsp3 : lookupName S3.env "%sp.0.ph1403"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide)
      (lookupName_cons_other _ _ _ (by decide)
        (lookupName_cons_other _ _ _ (by decide) hspH))
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_ifThen35peel L3.inv' rfl
      hsp3 hspLe32
  have hsp4 : lookupName S4.env "%sp.0.ph1403"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide)
      (lookupName_cons_other _ _ _ (by decide)
        (lookupName_cons_other _ _ _ (by decide)
          (lookupName_cons_other _ _ _ (by decide) hspH)))
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd45peel L4.inv' rfl
      hsp4 hspNe32
  have h1_5 : lookupName S5.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact h1H
  have hfr5 : lookupName S5.env "%frame.0.ph1402"
      = some (.int 8 (BitVec.ofNat 8 fr)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hfrH
  have hstk5 : lookupName S5.env "%stk" = some (.ptr K.stk) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have hv1pos : 1 ≤ (BitVec.ofNat 64 sp).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sp < 2 ^ 64)]
    exact hspPos
  have hv1le : (BitVec.ofNat 64 sp).toNat ≤ 519 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sp < 2 ^ 64)]
    exact hspLe
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_ifThen47peel (calls := calls) L5.inv' rfl h1_5 hfr5 hstk5 hv1pos hv1le
  have hinc6 : lookupName S6.env "%inc.peel"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hnep6 : lookupName S6.env "%nep"
      = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_ifEnd51peel L6.inv'
      rfl
      hinc6 hnep6 hult
  have hinc7 : lookupName S7.env "%inc.peel"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hep7 : lookupName S7.env "%ep" = some (.ptr K.ep) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hb7 : lookupName S7.env "%b" = some (.ptr K.b) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hbPtr
  have L8 : Stage2NoEventWalkLink calls K mem S7 K S8 :=
    link_ifEnd327peel (bs1 := [nextByte]) L7.inv'
      rfl
      hinc7 hep7 hb7 hkincLt hlaneW hval4lt hbyte1W
      (by rw [stage2NoEventWalkBytesToNat_single]; exact hb1)
  have hpre8 : S8.pre = some "if.end327.peel" := rfl
  have hsp8 : lookupName S8.env "%sp.0.ph1403"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hspH
  have hk8 : lookupName S8.env "%k.0.ph1404"
      = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h.kEq
  have htr8 : lookupName S8.env "%terms.0.ph1407"
      = some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h.termsPhi
  have htok8 : lookupName S8.env "%tokens.0.ph1408"
      = some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h.tokensPhi
  have L9 : Stage2NoEventWalkLink calls K mem S8 Kc S9 :=
    link_ifThen334 L8.inv' rfl hpre8
      hsp8 hk8 htr8 htok8 (Stage2NoEventWalkInv.tok_add_le h.inv h.count hkbound)
  have hpre9 : S9.pre = some "if.then334" := rfl
  have hnd9 : ((ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
      (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)).map (·.1)).Nodup := by
    simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have hsp9' : lookupName S9.env "%sp.0.lcssa1096.wide"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%sp.0.lcssa1096.wide") (v := .int 32 (BitVec.ofNat 32 sp))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  have hinc335 : lookupName S9.env "%inc335"
      = some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    have hc : lookupName S9.env "%inc335"
        = some (.int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2)) := by
      simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
        stage2NoEventWalkStored]
      exact stage2NoEventWalkCells_some (cs := ifThen334AllCells
        (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms))
        (n := "%inc335") (v := .int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2))
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
    simpa only [stage2NoEventWalkOfNat_add] using hc
  have h8alen : lookupName S8.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.alenPhi
  have h8arena : lookupName S8.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.arenaPhi
  have halen9 : lookupName S9.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%alen.0.ph1405") (env := S8.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    exact h8alen
  have harena9 : lookupName S9.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%arena.0.ph1406") (env := S8.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    exact h8arena
  have hadd338 : lookupName S9.env "%add338"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)) := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%add338") (v := .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  have hinc337 : lookupName S9.env "%inc337"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%inc337") (v := .int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  have L10 : Stage2NoEventWalkLink calls Kc mem S9 Kc S10 :=
    link_closeArr (calls := calls) (K := Kc)
      L9.inv' rfl hpre9 hsp9' hinc335 halen9 harena9 hadd338 hinc337 hspNe32
  have hpre10 : S10.pre = some "close_arr" := rfl
  have hnd10 : ((closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
      (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
      (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)).Nodup := by
    simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have hsp10 : lookupName S10.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%sp.3") (v := .int 32 (BitVec.ofNat 32 sp))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have h8stk : lookupName S8.env "%stk" = some (.ptr K.stk) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have h9stk : lookupName S9.env "%stk" = some (.ptr K.stk) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%stk") (env := S8.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    exact h8stk
  have hstk10 : lookupName S10.env "%stk" = some (.ptr K.stk) := by
    simp only [S10, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%stk") (env := S9.env)
      (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; simp)]
    exact h9stk
  have hbytePop' : readBytes S10.mem
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs :=
    hbytePop
  have L11 : Stage2NoEventWalkLink calls Kc mem S10 Kc S11 :=
    link_ifThen350 (calls := calls) (K := Kc) (s := S10) (stk := K.stk)
      (sp3 := BitVec.ofNat 32 sp)
      (a := closeReadAddr K.stk (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat)
      (bs := bs) L10.inv' rfl hsp10 hstk10 hbytePop' rfl
  -- the run, at the eleven steps' own fuel
  have hrun : ∀ n, runFuel calls (11 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S11 := by
    intro n
    rw [show 11 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
      (1 + n)))))))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8,
      stage2NoEventWalkLink_runFuel L9, stage2NoEventWalkLink_runFuel L10,
      stage2NoEventWalkLink_runFuel L11]
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc S11 11 :=
    ⟨hrun, L11.inv'⟩
  -- the trace: the pair's two events
  have hbsOpen : K.bs[lane]? = some (0x5B : UInt8) := by
    have hy : byte = (0x5B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [hy] using hbs
  have hbsClose : K.bs[next]? = some (0x5D : UInt8) := by
    have hy : nextByte = (0x5D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
    simpa [hy] using hbs1
  have htrace' : Stage2NoEventWalkTrace Kc :=
    Stage2NoEventWalkTrace.emptyArray htrace hbsOpen hbsClose
  -- the endpoint's after-value selection at the `if.then350` edge
  have hnd11 : (popCells.map (·.1)).Nodup := by
    simp only [popCells, closeGepCells50, closeIdxCells50,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have h50 : lookupName S11.env "%50"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [S11, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := popCells)
      (n := "%50") (v := .int 8 (BitVec.ofNat 8 (bytesToNat bs)))
      (List.mem_cons.mpr (Or.inl rfl)) hnd11
  have hsp11 : lookupName S11.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%sp.3") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%sp.3") (v := .int 32 (BitVec.ofNat 32 sp))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have hk11 : lookupName S11.env "%k.5"
      = some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%k.5") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%k.5") (v := .int 64 (BitVec.ofNat 64 (k + 2)))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have halen11 : lookupName S11.env "%alen.7"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%alen.7") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%alen.7") (v := .int 64 (BitVec.ofNat 64 K.arena.length))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have harena11 : lookupName S11.env "%arena.9"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%arena.9") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%arena.9") (v := .int 64 (BitVec.ofNat 64 K.arenaWord))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have hterms11 : lookupName S11.env "%terms.7"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%terms.7") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%terms.7")
      (v := .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have htoks11 : lookupName S11.env "%tokens.7"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%tokens.7") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%tokens.7") (v := .int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  -- base lookups through the route's cell layers
  have hbase : Stage2NoEventWalkBaseLookups Kc S11 := by
    have hb0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := h.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) hb0
      (cs := [("%Pivot6", .int 1 0)]) (names := ["%Pivot6"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot", .int 1 1)]) (names := ["%Pivot"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf2", .int 1 1)]) (names := ["%SwitchLeaf2"]) rfl
      (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%exitcond.peel", .int 1 0)]) (names := ["%exitcond.peel"]) rfl
      (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%tobool46.not.peel", .int 1 0)])
      (names := ["%tobool46.not.peel"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := [("%arrayidx50.peel", .ptr (bracketPushAddr K (BitVec.ofNat 64 sp))),
        ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615))])
      (names := ["%arrayidx50.peel", "%4"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase (K := K) b6
      (cs := [("%cmp319.not.peel", .int 1 1)]) (names := ["%cmp319.not.peel"]) rfl
      (by decide)
    have b8 := stage2NoEventCycleBase (K := K) b7
      (cs := [("%cmp332.peel", .int 1 1),
        ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))),
        ("%arrayidx330.peel", .ptr (K.b +
          (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
        ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4))])
      (names := ["%cmp332.peel", "%6", "%arrayidx330.peel", "%idxprom329.peel", "%5",
        "%arrayidx328.peel"]) rfl (by decide)
    have b9 := stage2NoEventCycleBase (K := K) b8
      (cs := ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
        (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := (ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
        (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)).map (·.1)) rfl
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b10 := stage2NoEventCycleBase (K := K) b9
      (cs := closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (names := (closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)) rfl
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b11 := stage2NoEventCycleBase (K := K) b10
      (cs := popCells) (names := popCells.map (·.1)) rfl
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)
    exact b11
  refine ⟨S11, Kc, rfl, hseg, ⟨?_⟩⟩
  refine ⟨L11.inv', rfl, bytesToNat bs, stage2NoEventWalkBytesToNat_lt hbsLen,
    by rw [hbsVal]; omega, sp, hspLt, by omega, hk63, hlt,
    Stage2NoEventWalkCount.step (a := 2) (b := 2) h.count rfl rfl (by omega), ?_,
    hbase, h.bPos, htrace', ?_⟩
  · refine ⟨"if.then350", rfl, ?_⟩
    refine PhiSelects.cons (op := .reg "%50") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [Kc, stateAt, evalOperand, h50, hsp11, hk11, halen11, harena11,
        hterms11, htoks11, stage2NoEventWalkOfNat_add]
  · intro q hq
    exact hcomma q hq


/-! ### The container instance: the empty array pair

The row at a head whose lane is `[` and whose next entry's lane is `]`.  The
route is the eleven blocks above, at the pair's carry (`tok + 2`, `terms + 7`);
the endpoint is `after_value` at index `k + 2`; the cycle returns to the head at
`k + 3`.  The class leg's price is discharged against its own two-entry advance,
`11 + Φ Kc (k+2) ≤ Φ K k`, and the cycle's eight against `Φ Kc (k+3)`.
-/

/-- **The empty array pair's continuing row**: the head at `[`, the route to
`after_value`, and the cycle to the head at `k + 3`, as a
`Stage2NoEventWalkRow.cont`.

The route's staging is the pair's own: the head's depth, frame and zero
extension, the post-push entry lane and document byte at the closer, and the
popped stack byte.  `hcomma` is the separator the cycle reads at the endpoint's
index.  The row advances three entries, so `k + 3` is the next head's index and
must be below the entry count. -/
noncomputable def stage2NoEventWalkRow_cont_bracketPair {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (h1H : lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrLt : fr < 2 ^ 8) (hfrPos : 1 ≤ fr)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let w :=
    stage2NoEventWalkBracketPairLeg (calls := calls) h htrace hk hbs hb hk1 hbs1 hb1
      hspH hfrH h1H
      hspPos hspLe hspLt hfrLt hfrPos hkbound hlaneW hval4lt hbyte1W hbytePop
      hbsLen hbsVal hcomma hlt hk63
  let sE := Classical.choose w
  have hspec := Classical.choose_spec w
  let Kc := Classical.choose hspec
  have hspecK := Classical.choose_spec hspec
  have hKc : Kc = { K with tok := K.tok + 2, terms := K.terms + 7 } := hspecK.1
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc sE 11 := hspecK.2.1
  have hsrc : Stage2NoEventWalkCycleSrc calls mem Kc (k + 2) sE :=
    Classical.choice hspecK.2.2
  let cw := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' := Classical.choose cw
  have hcwspec := Classical.choose_spec cw
  let p := Classical.choose hcwspec
  have hcyc : Stage2NoEventWalkCycle calls mem Kc (k + 2) sE 1 s' p :=
    Classical.choose_spec hcwspec
  refine stage2NoEventWalkRow_cont_of_afterValue (F := F) hseg hsrc hcyc ?_ ?_ ?_
    (by omega) ?_
  · rw [hKc]
  · rw [hKc]
  · rw [hKc]
  -- the class leg's price, against the route's own two-entry advance
  · have hpot : stage2NoEventWalkPotential Kc (k + 2) =
        stage2NoEventWalkPotential K (k + 2) := by
      rw [hKc]
      rfl
    rw [hpot]
    have hk2 : k + 2 ≤ K.nep := by omega
    have hlen : K.ent.length = K.nep :=
      readLanes32_length mem K.ep K.nep K.ent h.inv.entries
    have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 2) 0 :=
      stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
    have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 2) hk2 hentle
    omega

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkOfNat_add
#print axioms stage2NoEventWalkBytesToNat_lt
#print axioms stage2NoEventWalkRow_cont_of_afterValue
#print axioms stage2NoEventWalkBracketPairLeg
#print axioms stage2NoEventWalkRow_cont_bracketPair

end LeanLLVM.Refinement
