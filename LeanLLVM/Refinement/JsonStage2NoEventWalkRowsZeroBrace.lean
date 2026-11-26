/-
The no-event walk's depth-zero brace descend.

`JsonStage2NoEventWalkRowsZeroDescend` supplies the bracket arm at `%sp = 0`.
The brace's arm is the same shape: at a zero depth `if.end19`'s `%tobool.not`
reads one, `if.then20` is never entered, and the `{` route reaches `NodeBlock21`
with no stack write at all.  The committed brace exports cannot serve it —
`stage2NoEventWalkBracePrologue`, `stage2NoEventWalkKeyRoute_of_head`,
`stage2NoEventWalkEntryAPrologueFromEnd19` and
`stage2NoEventWalkBraceDescendRow_quote` all take `1 ≤ sp` and read at
`writeBytes s.mem (bracePushAddr K sp) …`, a write this route never makes.

**The route.**  Seven links from the head: the three-block dispatch
(`NodeBlock5` → `NodeBlock` → `LeafBlock3` → `if.then9`), `if.then9`'s seven
`phi`s at the carried depth (`link_braceIfThen9_false`, whose depth guard holds
at zero), `if.end19`'s zero arm (`link_ifEnd19_true`), `if.end23`'s live test,
and `if.end74`'s next-entry read — all at the head's own memory.  The cells it
binds at `NodeBlock21` are the committed exporter's
(`Stage2NoEventWalkBracePrologueCells`), with `%inc24 = 0 + 1`: the same cells
the pushed route binds at `sp + 1`.

**Why the key route composes unchanged.**  `stage2NoEventWalkKeyRoute_of_leafBlock17`
is stated at the state's own memory (`s.mem`, and the call's supplies at
`writeBytes (writeBytes s.mem …) …`), so it consumes this prologue directly: the
prologue leaves memory and cursor untouched (`mem_eq`/`next_eq`) and the row's
call supplies are the positive row's, minus the push reads.

**The price.**  Seven links plus the key route's ten plus the committed pair
cycle's three: `7 + 10 + 3 = 20 ≤ 32 · 4 = 128`, so the row is a `cont` to the
head at `k + 4` with no price premise.

**What stays a hypothesis.**  The key route's own supplies (the two lifetime
markers, the scanner call and its frame, the endpoint's trace, the colon's byte),
the scratch guard, the room `k + 4 < K.nep`, and — at positive depth — the
positive arm's row, which reads the pushed memory.  `Stage2NoEventWalkZeroDescendBranch`
is the bracket arm's predicate unchanged: it is a fact about the depth word and
grows no field here.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsZeroDescend
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsBrace
import LeanLLVM.Refinement.JsonStage2NoEventWalkKeyRoute
import LeanLLVM.Refinement.JsonStage2NoEventWalkCyclePairA

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval (cells)

/-! ### The zero prologue's output

The head's seven links, their segment, the memory and cursor they leave, and the
exporter's cells at `NodeBlock21`.  `sp` is the depth `%inc24` carries; at the
zero depth it is one, the depth the pushed route carries one above its push.
-/

/-- **The state the `{` head's seven zero-depth links hand over**. -/
structure Stage2NoEventWalkBraceZeroPrologueOut (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (b lane sp : Nat) : Type where
  s' : State
  seg : Stage2NoEventWalkSegment calls mem K s K s' 7
  mem_eq : s'.mem = s.mem
  next_eq : s'.next = s.next
  cells : Stage2NoEventWalkBracePrologueCells K mem k s' b lane sp

/-- **The `{` head's seven links at the zero depth**, to `NodeBlock21`'s entry
with the prologue's cells: the dispatch, the carried-depth `if.then9` (no push),
`if.end19`'s zero arm, `if.end23`'s live test, and the next entry's read.  The
lane is the entry at `k + 1`'s word, the byte's value `nextByte.toNat`, and the
depth one. -/
theorem stage2NoEventWalkBraceZeroPrologue {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    {lane : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hbranch : Stage2NoEventWalkZeroDescendBranch s)
    {next : Nat} (hk1 : K.ent[k + 1]? = some next)
    (hbs1 : K.bs[next]? = some nextByte) :
    Nonempty (Stage2NoEventWalkBraceZeroPrologueOut calls mem K k s
      nextByte.toNat next 1) := by
  classical
  obtain ⟨sp, fr, hspH, hfrH, -, hspLt, -⟩ := h.spPhiBounded
  have hspZero : sp = 0 := by
    have hres := hbranch.sp_zero hspH
    rw [Nat.mod_eq_of_lt hspLt] at hres
    exact hres
  subst hspZero
  have h3H : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    h.braceCell hk hbs hb
  have hkH : lookupName s.env "%k.0.ph1404" =
      some (.int 64 (BitVec.ofNat 64 k)) := h.kEq
  have htrH : lookupName s.env "%terms.0.ph1407" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := h.termsPhi
  have htokH : lookupName s.env "%tokens.0.ph1408" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := h.tokensPhi
  have halenH : lookupName s.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := h.alenPhi
  have harenaH : lookupName s.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := h.arenaPhi
  have hnepH : lookupName s.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := h.nepI
  have hepH : lookupName s.env "%ep" = some (.ptr K.ep) := h.epPtr
  have hbH : lookupName s.env "%b" = some (.ptr K.b) := h.bPtr
  obtain ⟨laneR, _, -, -, -, -, -, hidxH, hincH, -, -, -⟩ := h.laneRead
  let spv : BitVec 32 := BitVec.ofNat 32 0
  let frv : BitVec 8 := BitVec.ofNat 8 fr
  let k64 : BitVec 64 := BitVec.ofNat 64 k
  let termsv : BitVec 64 := BitVec.ofNat 64 K.terms
  let tokv : BitVec 64 := BitVec.ofNat 64 K.tok
  let nep64 : BitVec 64 := BitVec.ofNat 64 K.nep
  let inc : BitVec 64 := BitVec.ofNat 64 (k + 1)
  let idx : BitVec 64 := BitVec.ofNat 64 laneR
  have hspvZero : spv.toNat = 0 := by
    simp only [spv, BitVec.toNat_ofNat]
  -- the three dispatch blocks
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h.inv h.pc h3H (by decide)
  have h3_1 : lookupName S1.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3H
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 0) :: S1.env) S1 "LeafBlock3"
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3_1 (by decide)
  have h3_2 : lookupName S2.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3_1
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 1) :: S2.env) S2 "if.then9"
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock3_true L2.inv' (by simp only [S2, stage2NoEventWalkNext]) h3_2 (by decide)
  -- the head edge's `phi` inputs, at the dispatch's environment
  have hk3 : lookupName S3.env "%k.0.ph1404" = some (.int 64 k64) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hkH
  have hinc3 : lookupName S3.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hidx3 : lookupName S3.env "%idxprom.peel" = some (.int 64 idx) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidxH
  have hfr3 : lookupName S3.env "%frame.0.ph1402" = some (.int 8 frv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfrH
  have hsp3 : lookupName S3.env "%sp.0.ph1403" = some (.int 32 spv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hspH
  have htr3 : lookupName S3.env "%terms.0.ph1407" = some (.int 64 termsv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htrH
  have htok3 : lookupName S3.env "%tokens.0.ph1408" = some (.int 64 tokv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokH
  have hguard : evalICmp .ugt spv (BitVec.ofNat 32 519) = (0 : BitVec 1) :=
    stage2NoEventUgt519_zero (by rw [hspvZero]; omega)
  -- `if.then9` at the zero depth
  let S4 := stage2NoEventWalkNext
    (braceIfThen9Cells S3.env inc idx frv spv k64 termsv tokv) S3 "if.end19"
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_braceIfThen9_false L3.inv' rfl rfl hk3 hinc3 hidx3 hfr3 hsp3 htr3 htok3 hguard
  have hsp4 : lookupName S4.env "%sp.0.lcssa1092.wide" = some (.int 32 spv) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- `if.end19`'s zero arm, no stack write
  let S5 := openZeroEnd23 S4
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd19_true L4.inv' rfl hsp4 hspvZero
  have hsp5 : lookupName S5.env "%sp.0.lcssa1092.wide" = some (.int 32 spv) := by
    simp only [S5, openZeroEnd23, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp4
  have hinc5 : lookupName S5.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S5, S4, S3, S2, S1, openZeroEnd23, stage2NoEventWalkNext,
      braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hnep5 : lookupName S5.env "%nep" = some (.int 64 nep64) := by
    simp only [S5, S4, S3, S2, S1, openZeroEnd23, stage2NoEventWalkNext,
      braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnepH
  have hk1nep : k + 1 < K.nep := by
    have hlen : K.ent.length = K.nep :=
      readLanes32_length mem K.ep K.nep K.ent h.inv.entries
    have hi : k + 1 < K.ent.length := (List.getElem?_eq_some_iff.mp hk1).1
    omega
  have hnepLt : K.nep < 2 ^ 64 := h.inv.nepLt
  have hk1max : k + 1 < 2 ^ 32 := by
    have hmaxDoc : K.n ≤ 2 ^ 32 := by
      have := h.inv.maxDoc
      simpa [stage2MaxDocument] using this
    have hnepDoc : K.nep ≤ 2 ^ 32 := le_trans h.inv.nepLe hmaxDoc
    omega
  have hincNat : inc.toNat = k + 1 := by
    simp only [inc, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
  have hult : BitVec.ult inc nep64 = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    rw [hincNat, show nep64.toNat = K.nep from by
      simp only [nep64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnepLt]]
    omega
  -- `if.end23` and the next entry's read
  let S6 := openZeroEnd74 S4 spv
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_ifEnd23 L5.inv' rfl hsp5 hinc5 hnep5 hult
  have hterms6 : lookupName S6.env "%terms.0.lcssa1080" = some (.int 64 termsv) := by
    simp only [S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htok6 : lookupName S6.env "%tokens.0.lcssa1074" = some (.int 64 tokv) := by
    simp only [S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hep6 : lookupName S6.env "%ep" = some (.ptr K.ep) := by
    simp only [S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hepH
  have hb6 : lookupName S6.env "%b" = some (.ptr K.b) := by
    simp only [S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbH
  have hinc6 : lookupName S6.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hm6 : S6.mem = s.mem := by
    simp only [S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext]
  have hincLt : inc.toNat < 2 ^ 63 := by
    rw [hincNat]
    omega
  obtain ⟨bs4, hlane, hval4, hval4lt, hbyte1⟩ :=
    stage2NoEventWalkBracketZeroDescendReads h hk1 hbs1
  let S7 := stage2NoEventWalkNext
    (ifEnd74Out S6.env K.ep K.b termsv tokv inc bs4 [nextByte]) S6 "NodeBlock21"
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_ifEnd74 L6.inv' rfl hterms6 htok6 hep6 hb6 hinc6 hincLt
      (by rw [hm6]; exact hlane) hval4lt (by rw [hm6]; exact hbyte1)
  -- the prologue's cells at `NodeBlock21`'s entry
  have h11 : lookupName S7.env "%11" =
      some (.int 8 (BitVec.ofNat 8 nextByte.toNat)) := by
    simp only [S7, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells,
      stage2NoEventWalkBytesToNat_single]
    rw [lookupName_cons_self]
  have h10c : lookupName S7.env "%10" =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) := by
    simp only [S7, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hinc24 : lookupName S7.env "%inc24" =
      some (.int 32 (BitVec.ofNat 32 (0 + 1))) := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    simp only [spv, stage2NoEventWalkOfNat_add]
  have hk7 : lookupName S7.env "%k.0.lcssa1086" = some (.int 64 k64) := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htrPhi : lookupName S7.env "%terms.0.lcssa1080" = some (.int 64 termsv) := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htokPhi : lookupName S7.env "%tokens.0.lcssa1074" = some (.int 64 tokv) := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen7 : lookupName S7.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halenH
  have harena7 : lookupName S7.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harenaH
  have hadd : lookupName S7.env "%add" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 1))) := by
    simp only [S7, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    simp only [termsv, stage2NoEventWalkOfNat_add]
  have hinc26 : lookupName S7.env "%inc26" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [S7, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    simp only [tokv, stage2NoEventWalkOfNat_add]
  -- the base table through the seven links' cell layers
  have hbase : Stage2NoEventWalkBaseLookups K S7 := by
    have hb0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := h.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) hb0
      (cs := [("%Pivot6", .int 1 0)]) (names := ["%Pivot6"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot", .int 1 0)]) (names := ["%Pivot"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf4", .int 1 1)]) (names := ["%SwitchLeaf4"]) rfl (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%cmp10", .int 1 0), ("%tokens.0.lcssa1074", .int 64 tokv),
        ("%terms.0.lcssa1080", .int 64 termsv), ("%k.0.lcssa1086", .int 64 k64),
        ("%sp.0.lcssa1092.wide", .int 32 spv), ("%frame.0.lcssa1098", .int 8 frv),
        ("%idxprom.lcssa1108", .int 64 idx), ("%inc.lcssa1129", .int 64 inc)])
      (names := ["%cmp10", "%tokens.0.lcssa1074", "%terms.0.lcssa1080",
        "%k.0.lcssa1086", "%sp.0.lcssa1092.wide", "%frame.0.lcssa1098",
        "%idxprom.lcssa1108", "%inc.lcssa1129"])
      rfl (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%tobool.not", .int 1 1)])
      (names := ["%tobool.not"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := [("%cmp66.not", .int 1 1),
        ("%inc24", .int 32 (spv + BitVec.ofNat 32 1))])
      (names := ["%cmp66.not", "%inc24"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase (K := K) b6
      (cs := ifEnd74Cells K.ep K.b termsv tokv inc bs4 [nextByte])
      (names := ["%11", "%arrayidx77", "%idxprom76", "%10", "%arrayidx75",
        "%inc26", "%add"]) rfl (by decide)
    intro n v hv
    exact b7 n v hv
  -- the run, at the seven links' own fuel
  have hrun : ∀ n, runFuel calls (7 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S7 := by
    intro n
    rw [show 7 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + n)))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7]
  have hmem : S7.mem = s.mem := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext]
  have hnext : S7.next = s.next := by
    simp only [S7, S6, S4, S3, S2, S1, openZeroEnd74, openZeroEnd23,
      stage2NoEventWalkNext]
  refine ⟨⟨S7, ⟨hrun, L7.inv'⟩, hmem, hnext, ?_⟩⟩
  exact
    { inv := L7.inv'
      pc := rfl
      laneLt := by rw [← hval4]; exact hval4lt
      spLt := by omega
      h11 := h11
      h10 := by rw [← hval4]; exact h10c
      hinc24 := hinc24
      hk := hk7
      htermsPhi := htrPhi
      htokPhi := htokPhi
      halen := halen7
      harena := harena7
      hadd := hadd
      hinc26 := hinc26
      hbase := hbase
      bPos := h.bPos
      count := h.count }

/-! ### The depth-zero `{` descend arm as a row

The head's seven-link prologue (proved above), `NodeBlock21`'s entry A (the
committed cells, at the opening quote), the committed key route (ten), and the
committed pair cycle (three): a `cont` to the head at `k + 4`, priced `20 ≤ 128`.
-/

/-- **The depth-zero `{` descend arm as a row.**  Beyond `Head` and the class: the
zero staging, the entry at `k + 1` and its opening quote (`nextByte.toNat = 34`),
the room `k + 4 < K.nep`, the separator at `k + 3`, the scratch guard and the key
route's own supplies — the positive row's list minus the push reads, which the
prologue's `mem_eq` removes. -/
noncomputable def stage2NoEventWalkBraceZeroDescendRow {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBraceClass K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 34)
    (hbranch : Stage2NoEventWalkZeroDescendBranch s)
    (hvAddr : k + 4 < 2 ^ 63) (hvNext : k + 4 < K.nep)
    (hscratch : evalICmp .ugt
      (BitVec.ofNat 64 (K.ent.getD (k + 2) 0) +
        (BitVec.ofNat 64 (BitVec.ofNat 32 next).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0)
    (r0 : CallOutcome)
    (hstart : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] s.mem s.next = some r0)
    (hstartMem : r0.mem = s.mem) (hstartNext : r0.next = s.next)
    (r : CallOutcome)
    (hcall : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + next),
       .int 64 (keySub next (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) s.next = some r)
    (hrRet : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcallInv : Stage2NoEventWalkInv K mem
      { s with mem := r.mem, next := r.next })
    (lend : CallOutcome)
    (hlend : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next = some lend)
    (hlendMem : lend.mem = r.mem)
    (htraceEnd : Stage2NoEventWalkTrace
      (keyCarry K next (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1)))
    (hcolon : ∀ lane, K.ent[k + 3]? = some lane → K.bs.getD lane 0 = 58) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  obtain ⟨P⟩ :=
    stage2NoEventWalkBraceZeroPrologue (calls := calls) h hent hbs hb hbranch hk1 hbs1
  let A : Stage2NoEventWalkEntryAPrologue K mem k P.s' := P.cells.toEntryA hb1
  have hAlane : A.lane = next := by
    simp only [A, Stage2NoEventWalkBracePrologueCells.toEntryA]
  obtain ⟨sE, hsegKey, hpairNe⟩ :=
    stage2NoEventWalkKeyRoute_of_leafBlock17 (calls := calls) (mem := mem)
      (K := K) (k := k) (s := P.s') A hvAddr hvNext
      (by rw [hAlane]; exact hscratch) r0
      (by rw [P.mem_eq, P.next_eq]; exact hstart)
      (by rw [P.mem_eq]; exact hstartMem)
      (by rw [P.next_eq]; exact hstartNext) r
      (by rw [P.mem_eq, P.next_eq, hAlane]; exact hcall)
      hrRet (Stage2NoEventWalkInv.mem_congr hcallInv rfl) lend hlend hlendMem
      (by rw [hAlane]; exact htraceEnd) hcolon
  rw [hAlane] at hpairNe
  obtain ⟨s', hcyc⟩ :=
    stage2NoEventWalkCycle_of_pair_price (calls := calls) (mem := mem)
      (K := keyCarry K next (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
      (k := k) (s := sE) (Classical.choice hpairNe)
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hent : K.ent.getD k 0 ≤ K.ent.getD (k + 4) 0 :=
    stage2NoEventEnt_getD_le (l := K.ent) h.inv.order (d := 0) (i := k) (j := k + 4)
      (by omega) (by rw [hlen]; omega)
  have hk4 : k + 4 ≤ K.nep := by omega
  have hdrop := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 4) hk4 hent
  have hpotEq : stage2NoEventWalkPotential
      (keyCarry K next (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
      (k + 4) = stage2NoEventWalkPotential K (k + 4) := rfl
  have hprice : 7 + 10 + 3 + stage2NoEventWalkPotential
      (keyCarry K next (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
      (k + 4) ≤ stage2NoEventWalkPotential K k := by
    rw [hpotEq]
    omega
  exact ⟨Stage2NoEventWalkRow.cont
    (keyCarry K next (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
    (k + 4) s' (7 + 10 + 3)
    { seg :=
        { seg := (P.seg.trans hsegKey).trans hcyc.headPriced.seg.seg
          head' := hcyc.headPriced.seg.head'
          trace' := hcyc.headPriced.seg.trace' }
      credit := hprice }
    rfl rfl rfl (by omega) hvNext⟩

/-- **The `{` class's descend arm at whichever depth the head holds**: the
depth-zero route when the head's depth word reads zero, the positive arm's row
otherwise.  The split is on the word's residue, `Decidable` and so eliminable
into the row's `Type`; at a zero residue the zero staging is the head's own cell
(`Stage2NoEventWalkZeroDescendBranch.of_cell`), and at a non-zero residue the
positive row is the caller's.  A class producer fills
`stage2NoEventWalkBraceReady_of_routes`'s `hdescend` slot with this: the
depth-zero case is the head's own cell and the zero row, the positive case is
the caller's `hpos`, and both carry the zero row's other premises — the key
route's supplies (`hscratch`, the two lifetime markers, the scanner call and its
frame, the endpoint's trace), the colon's byte, the room and the entry at
`k + 1` — which the slot takes at every depth. -/
noncomputable def stage2NoEventWalkBraceDescendRow_of_cell {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBraceClass K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 34)
    {sp : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hpos : sp % 2 ^ 32 ≠ 0 → Stage2NoEventWalkRow calls mem F K k s)
    (hvAddr : k + 4 < 2 ^ 63) (hvNext : k + 4 < K.nep)
    (hscratch : evalICmp .ugt
      (BitVec.ofNat 64 (K.ent.getD (k + 2) 0) +
        (BitVec.ofNat 64 (BitVec.ofNat 32 next).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0)
    (r0 : CallOutcome)
    (hstart : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] s.mem s.next = some r0)
    (hstartMem : r0.mem = s.mem) (hstartNext : r0.next = s.next)
    (r : CallOutcome)
    (hcall : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + next),
       .int 64 (keySub next (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) s.next = some r)
    (hrRet : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcallInv : Stage2NoEventWalkInv K mem
      { s with mem := r.mem, next := r.next })
    (lend : CallOutcome)
    (hlend : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next = some lend)
    (hlendMem : lend.mem = r.mem)
    (htraceEnd : Stage2NoEventWalkTrace
      (keyCarry K next (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1)))
    (hcolon : ∀ lane, K.ent[k + 3]? = some lane → K.bs.getD lane 0 = 58) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  by_cases hz : sp % 2 ^ 32 = 0
  · exact stage2NoEventWalkBraceZeroDescendRow h hclass hk1 hbs1 hb1
      (Stage2NoEventWalkZeroDescendBranch.of_cell hspH hz) hvAddr hvNext hscratch
      r0 hstart hstartMem hstartNext r hcall hrRet hcallInv lend hlend hlendMem
      htraceEnd hcolon
  · exact hpos hz

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkBraceZeroPrologueOut
#print axioms stage2NoEventWalkBraceZeroPrologue
#print axioms stage2NoEventWalkBraceZeroDescendRow
#print axioms stage2NoEventWalkBraceDescendRow_of_cell

end LeanLLVM.Refinement
