/-
The no-event walk's value class, from its entry: `scalar`'s post-`phi` branch to
the arms.

`JsonStage2NoEventWalkEntryRooted` proves the scalar class's two-block head from
`scalar.loopexit` to `cond.true` (the end test taken) and `cond.end` (not taken),
and `JsonStage2NoEventWalkRowsValue` composes the value class's row from a
`Stage2NoEventWalkValueRoute` laid out from a `Stage2NoEventWalkHead` at
`NodeBlock5`.  The tree's value producers are all rooted at that head —
`stage2NoEventWalkValueProv_of_head`, `…ValueRoute_of_head`, `…ValueRow_of_head`
and the four per-arm row wrappers (`…ValueRow_number`/`_literalTrue`/`_literalFalse`/`_literalNull`) take a `Head`'s `%inc.peel`/`%idxprom.peel`/`%3` cells —
so none of them can start at the head's own conclusion, which is already past
`scalar` and binds the `scalar` cells instead.

This module closes that gap.  From a generic `cond.true`/`cond.end` state — the
entry head's conclusion, whose registers are the scalar block's nine cells (the seven `phi`s plus `%cmp436` and `%arrayidx6.le1046`) — it runs
the route the fixture takes:

* `cond.true`: the next entry's lane word (`%arrayidx438`, `%56`, `%conv439`) into
  `cond.end`;
* `cond.end`: `%cond` (the `cond.true` edge's word, or `%n` on the untaken end
  test), and the extent test `%cmp443 = ugt %cond %idxprom.lcssa` into
  `land.lhs.true` (taken — the entry starts inside the document, so the `scalar`
  edge's `%cond = %n` is always above `%idxprom.lcssa`);
* `land.lhs.true` → the whitespace scan, `if.end457`'s `%ee.1` selection and
  `%k219` store, and `%or.cond901` → `if.then471` or `if.else495`, which is
  `JsonStage2NoEventWalkScalar`'s `stage2NoEventWalkScalarSkip`.

The result is the class route's provider half stated at the arm's entry: the
segment, the fourteen registers the arms read, the scan's stop `q` and bound
`%cond`, the two `phi` words, the measured count, and the entry chain's base
table transported through the scan's frame.

**What this module proves, and what is the caller's.**  `proved here`: the
`cond.true` and `cond.end` steps and the register transport into `land.lhs.true`
(`stage2NoEventWalkValueProviderAt_condTrue`/`…_condEnd`, via
`stage2NoEventWalkValueLand`), their composition with the entry head's two links
and the base-table transport (`stage2NoEventWalkValueEntry_true`,
`stage2NoEventWalkValueProv_of_entry_true`), and the row composition
(`stage2NoEventWalkValueRow_of_prov`).  `An existing
denotation`: the scan and the merge with its store and guard
(`stage2NoEventWalkScalarSkip`), the two `cond` links
(`link_condTrue`/`link_condEnd_fromCondTrue_true`/`link_condEnd_true`), the entry
links (`link_scalarLoopexitEntry`/`link_scalar_true`) and the value row's
head-free composition (`stage2NoEventWalkValueRow_cont_of_route_count`).  `The
caller's supply`: the entry state's invariant, its `%8`/`%indvars.iv`/`%inc`/`%7`/
`%terms.0`/`%tokens.0`/`%b`/`%nep` readings, the two loop-carried arena readings
`%alen.0.ph1405`/`%arena.0.ph1406` (the entry head's statement omits them), the
base table, the entry's lane and byte with its read, the next-entry fact, the
consumed-count bound, the arm route, its measured price, and `1 ≤ K.b`.

**The last entry.**  The `cond.end` provider is the same route with `%cond = %n`;
at a head with no next entry (`k + 1 = K.nep`) no continuing row exists — the row
composition needs `k + 2 < K'.nep` and the loop's own index bound rules that out —
so the `cond.end` arm's row is the terminal lane's, not this module's.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsValue
import LeanLLVM.Refinement.JsonStage2NoEventWalkEntryRooted

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The lane word at a state, from the invariant

`Stage2NoEventWalkHead.laneAt` reads an entry's position and the four bytes it
was read from using the head's invariant and nothing else.  The providers start
at a state that carries no head, so the same content is restated at the
invariant. -/

/-- **The lane word at an index, from the invariant alone.** -/
theorem Stage2NoEventWalkInv.laneWordAt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {i : Nat} (hi : i < K.nep) :
    ∃ q bs, K.ent[i]? = some q ∧ q < 2 ^ 32 ∧
      readBytes s.mem (K.ep + 4 * i) 4 = some bs ∧ bytesToNat bs = q := by
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep)
    (n := K.nep) (l := K.ent) h.entriesAt
  obtain ⟨q, bs, hq, hread, hval⟩ := hget i hi
  have hqlt : q < 2 ^ 32 := by
    have hinside := h.inside q (List.mem_of_getElem? hq)
    have := h.maxDoc
    simp only [stage2MaxDocument] at this
    omega
  exact ⟨q, bs, hq, hqlt, hread, hval⟩

/-! ### The base table's projections

The providers take the entry chain's stable live-ins as one table and read the
six pointers and two words the route needs.  Each is the table's entry at its own
name. -/

theorem stage2NoEventWalkBase_b {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%b" = some (.ptr K.b) :=
  h "%b" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem stage2NoEventWalkBase_ep {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%ep" = some (.ptr K.ep) :=
  h "%ep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem stage2NoEventWalkBase_n {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
  h "%n" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem stage2NoEventWalkBase_nep {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
  h "%nep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem stage2NoEventWalkBase_d {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%d" = some (.ptr K.d) :=
  h "%d" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem stage2NoEventWalkBase_k219 {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%k219" = some (.ptr (K.c + 32)) :=
  h "%k219" _ (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4])

theorem stage2NoEventWalkBase_gep1068 {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%invariant.gep1068" = some (.ptr (K.b - 1)) :=
  h "%invariant.gep1068" _ (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4])

theorem stage2NoEventWalkBase_ei {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) :
    lookupName s.env "%ei" = some (.ptr (K.next0 + 24)) :=
  h "%ei" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues])

/-! ### The land provider's shape

The route from `land.lhs.true` to the arm's entry, at the values the arms read.
`b` is the route's fixed cost, so that each layer above it can state its own
count against the scan's `b + 5·(q − lane)`. -/

/-- **The value provider's land route.**  The arm's entry, the scan's count and
its stop and bound, the counts' reading, the fourteen registers, and the entry
chain's table at the arm. -/
structure Stage2NoEventWalkValueLandProv (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k lane sp : Nat) (bv : BitVec 8) (s : State)
    (b : Nat) where
  /-- The arm's entry. -/
  e : State
  /-- The scan's counted route. -/
  j : Nat
  /-- The scan's stop. -/
  q : Nat
  /-- The scan's bound. -/
  cond : Nat
  seg : Stage2NoEventWalkSegment calls mem K s K e j
  /-- The merge's `%ee.1` selection. -/
  ee : lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q))
  regs : Stage2NoEventWalkValueArmsRegs K k lane sp 1 bv q cond e
  laneLeQ : lane ≤ q
  qLeCond : q ≤ cond
  condLeN : cond ≤ K.n
  qLt64 : q < 2 ^ 64
  condLt63 : cond < 2 ^ 63
  bound : j ≤ b + 5 * (q - lane)
  /-- The entry chain's table at the arm. -/
  base : Stage2NoEventWalkBaseLookups K e

/-! ### The land segment

`land.lhs.true` is `stage2NoEventWalkScalarSkip`'s entry: the probe, the scan, the
merge's selection and store, and the number-or-minus guard.  The segment carries
the invariant and the frame; the registers and the table are read back through
that frame. -/

/-- **The provider's land route** from `land.lhs.true`'s entry. -/
noncomputable def stage2NoEventWalkValueLand {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {k lane cond sp : Nat} {bv : BitVec 8}
    (hinv : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.lhs.true")
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 bv))
    (hinc : lookupName s.env "%inc.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfr : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 (BitVec.ofNat 8 1)))
    (htr : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hale : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harw : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hcondLeN : cond ≤ K.n)
    (hread0 : readByte s.mem ((K.b - 1) + cond) = some (K.bs.getD (cond - 1) 0))
    (hbytes : ∀ j, j < cond → readByte s.mem (K.b + j) = some (K.bs.getD j 0))
    (hidxlt : lane < cond) (hcondlt : cond < 2 ^ 63) :
    Stage2NoEventWalkValueLandProv calls mem K k lane sp bv s 12 := by
  classical
  have hb := stage2NoEventWalkBase_b hbase
  have hg := stage2NoEventWalkBase_gep1068 hbase
  have hk := stage2NoEventWalkBase_k219 hbase
  have hd := stage2NoEventWalkBase_d hbase
  have hei := stage2NoEventWalkBase_ei hbase
  choose e' jS q' hP using
    stage2NoEventWalkScalarSkip (calls := calls) (K := K) (mem := mem) (s := s)
      (g := K.b - 1) (b := K.b) (idx := lane) (cond := cond)
      (σ := fun j => K.bs.getD j 0) (u0 := K.bs.getD (cond - 1) 0)
      (inc := BitVec.ofNat 64 (k + 1)) (lc := bv) (k219 := K.c + 32)
      hinv hpc hg hcond hidx hb hinc hlc hk rfl hread0 hbytes hidxlt hcondlt
  obtain ⟨-, hpc', hee, hq1, hq2, -, -, hcount, hinv', -, hrun', hframe'⟩ := hP
  have hq64 : q' < 2 ^ 64 := by have h1 := hinv.nLt; omega
  have hbaseE' : Stage2NoEventWalkBaseLookups K e' := by
    intro n v hv
    have hmemB : n ∈ stage2NoEventWalkBaseNames := by
      have h := List.mem_map_of_mem (f := Prod.fst) hv
      rwa [stage2NoEventWalkBaseValues_names] at h
    rw [hframe' n (stage2NoEventWalkBaseNames_subset_skipFrame n hmemB)]
    exact hbase n v hv
  have hregs : Stage2NoEventWalkValueArmsRegs K k lane sp 1 bv q' cond e' :=
    { ee := hee
      idx := (hframe' "%idxprom.lcssa" (by decide)).trans hidx
      arr := (hframe' "%arrayidx6.le1046" (by decide)).trans harr
      b := (hframe' "%b" (by decide)).trans hb
      cond := (hframe' "%cond" (by decide)).trans hcond
      tokens := (hframe' "%tokens.0.lcssa1073" (by decide)).trans htok
      terms := (hframe' "%terms.0.lcssa1079" (by decide)).trans htr
      frame := (hframe' "%frame.0.lcssa1097" (by decide)).trans hfr
      sp := (hframe' "%sp.0.lcssa1091.wide" (by decide)).trans hsp
      inc := (hframe' "%inc.lcssa" (by decide)).trans hinc
      lcssa := (hframe' "%.lcssa" (by decide)).trans hlc
      alen := (hframe' "%alen.0.ph1405" (by decide)).trans hale
      arena := (hframe' "%arena.0.ph1406" (by decide)).trans harw
      d := (hframe' "%d" (by decide)).trans hd
      ei := (hframe' "%ei" (by decide)).trans hei }
  have hj12 : jS ≤ 12 + 5 * (q' - lane) := by
    rcases hcount with ⟨hj, -⟩ | ⟨hj, hqeq⟩ <;> omega
  exact
    { e := e', j := jS, q := q', cond := cond, seg := ⟨hrun', hinv'⟩, ee := hee,
      regs := hregs, laneLeQ := hq1, qLeCond := hq2, condLeN := hcondLeN,
      qLt64 := hq64, condLt63 := hcondlt, bound := hj12,
      base := hbaseE' }

/-! ### The `cond.true` provider

The end test is taken: `cond.true` loads the next entry's lane word and
`cond.end` tests it against this entry's position.  The stream is strictly
increasing, so the test takes and `%cond` is the next entry's position. -/

/-- **The value provider from `cond.true`**: the next entry's lane word, `%cond`,
the extent test, the scan, the merge's store and guard, to the arm's entry. -/
noncomputable def stage2NoEventWalkValueProviderAt_condTrue {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State} {k lane sp : Nat}
    {bv : BitVec 8}
    (hinv : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.true")
    (hent : K.ent[k]? = some lane)
    (hknext : k + 1 < K.nep) (hbPos : 1 ≤ K.b)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 bv))
    (hinc : lookupName s.env "%inc.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfr : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 (BitVec.ofNat 8 1)))
    (htr : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hale : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harw : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord))) :
    Stage2NoEventWalkValueLandProv calls mem K k lane sp bv s 14 := by
  classical
  have hk1lt64 : k + 1 < 2 ^ 64 := by have := hinv.nepLt; omega
  have hincpos : ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat = k + 1 := by
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1lt64]
  have hpos' : ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [hincpos]
    have h1 := hinv.nepLe
    have h2 := hinv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  choose q bs hLane using
    Stage2NoEventWalkInv.laneWordAt (K := K) (mem := mem) (s := s) hinv hknext
  have hentq : K.ent[k + 1]? = some q := hLane.1
  have hq32 : q < 2 ^ 32 := hLane.2.1
  have hread4 : readBytes s.mem (K.ep + 4 * (k + 1)) 4 = some bs := hLane.2.2.1
  have hqval : bytesToNat bs = q := hLane.2.2.2
  have hq64 : q < 2 ^ 64 := by omega
  choose hkltL hkval using List.getElem?_eq_some_iff.mp hent
  choose hqltL hqval' using List.getElem?_eq_some_iff.mp hentq
  have hord : lane < q := by
    have h := (List.pairwise_iff_getElem.mp hinv.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval'] at h
    exact h
  have hqltN : q < K.n := hinv.inside q (List.mem_of_getElem? hentq)
  have hq63 : q < 2 ^ 63 := by
    have hmax := hinv.maxDoc
    simp only [stage2MaxDocument] at hmax
    omega
  let S1 : State := stage2NoEventWalkNext
    (condTrueCells s.env
      (K.ep + ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat * 4) bs) s "cond.end"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_condTrue (calls := calls) (K := K) (mem := mem) (ep := K.ep)
      (inc := BitVec.ofNat 64 (k + 1)) (bs := bs) hinv hpc
      (stage2NoEventWalkBase_ep hbase) hinc hpos'
      (by rw [hincpos, Nat.mul_comm]; exact hread4)
  have hq32' : (BitVec.ofNat 32 q).toNat = q := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hconv : lookupName S1.env "%conv439" = some (.int 64 (BitVec.ofNat 64 q)) := by
    simp only [S1, stage2NoEventWalkNext, condTrueCells, hqval, hq32']
    rw [lookupName_cons_self]
  have hidx1 : lookupName S1.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [S1, stage2NoEventWalkNext, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx
  have hn64 : K.n < 2 ^ 64 := hinv.nLt
  have hlane64 : lane < 2 ^ 64 := by omega
  have hy2 : evalICmp .ugt (BitVec.ofNat 64 q) (BitVec.ofNat 64 lane) = 1 :=
    value_ugt_one hq64 hlane64 hord
  let S2 : State := stage2NoEventWalkNext
    (condEndCells S1.env (BitVec.ofNat 64 q) (BitVec.ofNat 64 lane)) S1
    "land.lhs.true"
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_condEnd_fromCondTrue_true (calls := calls) (K := K) (mem := mem)
      (c := BitVec.ofNat 64 q) (idx := BitVec.ofNat 64 lane) L1.inv'
      rfl (by simp only [S1, stage2NoEventWalkNext, hpc]) hconv hidx1 hy2
  have hcondL : lookupName S2.env "%cond" = some (.int 64 (BitVec.ofNat 64 q)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hidxL : lookupName S2.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx
  have harrL : lookupName S2.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harr
  have hlcL : lookupName S2.env "%.lcssa" = some (.int 8 bv) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hlc
  have hincL : lookupName S2.env "%inc.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hspL : lookupName S2.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hfrL : lookupName S2.env "%frame.0.lcssa1097" =
      some (.int 8 (BitVec.ofNat 8 1)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfr
  have htrL : lookupName S2.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htokL : lookupName S2.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have haleL : lookupName S2.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hale
  have harwL : lookupName S2.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S2, S1, stage2NoEventWalkNext, condEndCells, condTrueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harw
  have henv : S2.env = cells
      (condEndCells [] (BitVec.ofNat 64 q) (BitVec.ofNat 64 lane) ++
        condTrueCells [] (K.ep +
          ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat * 4) bs) s.env := rfl
  have hbaseS2 : Stage2NoEventWalkBaseLookups K S2 := by
    intro n v hv
    rw [henv]
    exact Stage2NoEventWalkBaseLookups.cellsOfNames
      (names := ["%cmp443", "%cond", "%conv439", "%56", "%arrayidx438"])
      hbase rfl
      (by decide : (["%cmp443", "%cond", "%conv439", "%56", "%arrayidx438"] :
        List String).all (fun n => decide (n ∉ stage2NoEventWalkBaseNames)) = true)
      n v hv
  have hqpos : 1 ≤ q := by omega
  have hread0 : readByte S2.mem ((K.b - 1) + q) =
      some (K.bs.getD (q - 1) 0) := by
    have haddr : (K.b - 1) + q = K.b + (q - 1) := by omega
    have hmem : S2.mem = s.mem := rfl
    rw [hmem, haddr]
    exact hinv.docByte (by omega)
  have hbytes : ∀ j, j < q → readByte S2.mem (K.b + j) = some (K.bs.getD j 0) := by
    intro j hj
    have hmem : S2.mem = s.mem := rfl
    rw [hmem]
    exact hinv.docByte (by omega)
  have hrunHL : ∀ n, runFuel calls (2 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S2 := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2]
  let p :=
    stage2NoEventWalkValueLand (calls := calls) (K := K) (mem := mem) (s := S2)
      (k := k) (lane := lane) (cond := q) (sp := sp) (bv := bv)
      L2.inv' rfl hcondL hidxL harrL hlcL hincL hspL hfrL htrL htokL haleL harwL
      hbaseS2 (le_of_lt hqltN) hread0 hbytes hord hq63
  exact
    { e := p.e, j := 2 + p.j, q := p.q, cond := q,
      seg := ⟨fun n => by
        rw [show 2 + p.j + n = 2 + (p.j + n) from by omega, hrunHL (p.j + n)]
        exact p.seg.run n, p.seg.inv'⟩,
      ee := p.ee, regs := p.regs, laneLeQ := p.laneLeQ, qLeCond := p.qLeCond,
      condLeN := le_of_lt hqltN, qLt64 := p.qLt64, condLt63 := hq63,
      bound := by have := p.bound; omega, base := p.base }

/-! ### The `cond.end` provider

The end test is not taken: `%cond` is `%n` on the `scalar` edge, and the extent
test always takes because the entry starts inside the document. -/

/-- **The value provider from `cond.end`** (the untaken end test's target):
`%cond = %n`, the extent test, the scan, the merge's store and guard, to the
arm's entry. -/
noncomputable def stage2NoEventWalkValueProviderAt_condEnd {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State} {k lane sp : Nat}
    {bv : BitVec 8}
    (hinv : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.end")
    (hpre : s.pre = some "scalar")
    (hent : K.ent[k]? = some lane)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 bv))
    (hinc : lookupName s.env "%inc.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfr : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 (BitVec.ofNat 8 1)))
    (htr : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hale : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harw : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hbPos : 1 ≤ K.b) :
    Stage2NoEventWalkValueLandProv calls mem K k lane sp bv s 14 := by
  classical
  have hn := stage2NoEventWalkBase_n hbase
  have hlaneN : lane < K.n := hinv.inside lane (List.mem_of_getElem? hent)
  have hn64 : K.n < 2 ^ 64 := hinv.nLt
  have hlane64 : lane < 2 ^ 64 := by omega
  have hyq : evalICmp .ugt (BitVec.ofNat 64 K.n) (BitVec.ofNat 64 lane) = 1 :=
    value_ugt_one hn64 hlane64 hlaneN
  let S2 : State := stage2NoEventWalkNext
    (condEndCells s.env (BitVec.ofNat 64 K.n) (BitVec.ofNat 64 lane)) s
    "land.lhs.true"
  have L1 : Stage2NoEventWalkLink calls K mem s K S2 :=
    link_condEnd_true (calls := calls) (K := K) (mem := mem)
      (c := BitVec.ofNat 64 K.n) (idx := BitVec.ofNat 64 lane) hinv hpc hpre hn hidx hyq
  have hcondL : lookupName S2.env "%cond" =
      some (.int 64 (BitVec.ofNat 64 K.n)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hidxL : lookupName S2.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx
  have harrL : lookupName S2.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harr
  have hlcL : lookupName S2.env "%.lcssa" = some (.int 8 bv) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hlc
  have hincL : lookupName S2.env "%inc.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hspL : lookupName S2.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hfrL : lookupName S2.env "%frame.0.lcssa1097" =
      some (.int 8 (BitVec.ofNat 8 1)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfr
  have htrL : lookupName S2.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htokL : lookupName S2.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have haleL : lookupName S2.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hale
  have harwL : lookupName S2.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S2, stage2NoEventWalkNext, condEndCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harw
  have henv : S2.env = cells
      (condEndCells [] (BitVec.ofNat 64 K.n) (BitVec.ofNat 64 lane)) s.env := rfl
  have hbaseS2 : Stage2NoEventWalkBaseLookups K S2 := by
    intro n v hv
    rw [henv]
    exact Stage2NoEventWalkBaseLookups.cellsOfNames
      (names := ["%cmp443", "%cond"]) hbase rfl
      (by decide : (["%cmp443", "%cond"] : List String).all
        (fun n => decide (n ∉ stage2NoEventWalkBaseNames)) = true) n v hv
  have hread0 : readByte S2.mem ((K.b - 1) + K.n) =
      some (K.bs.getD (K.n - 1) 0) := by
    have haddr : (K.b - 1) + K.n = K.b + (K.n - 1) := by omega
    have hmem : S2.mem = s.mem := rfl
    rw [hmem, haddr]
    exact hinv.docByte (by omega)
  have hbytes : ∀ j, j < K.n → readByte S2.mem (K.b + j) = some (K.bs.getD j 0) := by
    intro j hj
    have hmem : S2.mem = s.mem := rfl
    rw [hmem]
    exact hinv.docByte hj
  have hrunHL : ∀ n, runFuel calls (1 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S2 := by
    intro n
    rw [stage2NoEventWalkLink_runFuel L1]
  let p :=
    stage2NoEventWalkValueLand (calls := calls) (K := K) (mem := mem) (s := S2)
      (k := k) (lane := lane) (cond := K.n) (sp := sp) (bv := bv)
      L1.inv' rfl hcondL hidxL harrL hlcL hincL hspL hfrL htrL htokL haleL harwL
      hbaseS2 le_rfl hread0 hbytes hlaneN hinv.nLt63
  exact
    { e := p.e, j := 1 + p.j, q := p.q, cond := K.n,
      seg := ⟨fun n => by
        rw [show 1 + p.j + n = 1 + (p.j + n) from by omega, hrunHL (p.j + n)]
        exact p.seg.run n, p.seg.inv'⟩,
      ee := p.ee, regs := p.regs, laneLeQ := p.laneLeQ, qLeCond := p.qLeCond,
      condLeN := le_rfl, qLt64 := p.qLt64, condLt63 := hinv.nLt63,
      bound := by have := p.bound; omega, base := p.base }

/-! ### The entry head with its table

`JsonStage2NoEventWalkEntryRooted`'s scalar entry head returns the two-block
segment and the scalar block's nine cells (the seven `phi`s plus `%cmp436` and `%arrayidx6.le1046`) but not the entry chain's table at its
target, nor the two loop-carried arena readings the arms read.  `scalar.loopexit`'s
two links bind only `%55`, `%idxprom.le1291` and the nine `scalarCells`, none of
them a base name, so the table transports from the entry: this theorem is the
entry head's two links and cells plus that transport, with the `cond.true`
provider appended. -/

/-- **The entry head's two links and the provider at its target.** -/
structure Stage2NoEventWalkValueEntry (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k lane sp : Nat) (bv : BitVec 8) (s : State) where
  /-- The entry head's target. -/
  sE : State
  /-- The entry head's two links. -/
  seg : Stage2NoEventWalkSegment calls mem K s K sE 2
  /-- The provider at the entry head's target. -/
  prov : Stage2NoEventWalkValueLandProv calls mem K k lane sp bv sE 14

/-- **The value provider from `scalar.loopexit`, the end test taken.**  The entry
head's two links (with the base table and the arena readings transported to
`cond.true`), then the `cond.true` provider. -/
noncomputable def stage2NoEventWalkValueEntry_true {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State} {k lane : Nat}
    {iv : BitVec 64} {bv : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar.loopexit")
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (h8 : lookupName s.env "%8" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hinc : lookupName s.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hbv : lookupName s.env "%7" = some (.int 8 bv))
    (htr : lookupName s.env "%terms.0" = some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hent : K.ent[k]? = some lane) (hlane32 : lane < 2 ^ 32)
    (hknext : k + 1 < K.nep) (hbPos : 1 ≤ K.b) :
    Stage2NoEventWalkValueEntry calls mem K k lane (iv.toNat % 2 ^ 32) bv s := by
  classical
  let sp9 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let idx : BitVec 64 := BitVec.ofNat 64 (BitVec.ofNat 32 lane).toNat
  let S1 : State := stage2NoEventWalkNext
    (("%55", .int 32 sp9) :: ("%idxprom.le1291", .int 64 idx) :: s.env) s "scalar"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_scalarLoopexitEntry h hpc h8 hiv
  have hpc1 : S1.pc = "scalar" := rfl
  have hpre1 : S1.pre = some "scalar.loopexit" := by
    simp only [S1, stage2NoEventWalkNext, hpc]
  have hinc1 : lookupName S1.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hidx1 : lookupName S1.env "%idxprom.le1291" = some (.int 64 idx) := by
    simp only [S1, stage2NoEventWalkNext, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hbv1 : lookupName S1.env "%7" = some (.int 8 bv) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbv
  have hsp1 : lookupName S1.env "%55" =
      some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_self]
  have htr1 : lookupName S1.env "%terms.0" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htok1 : lookupName S1.env "%tokens.0" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hb1 : lookupName S1.env "%b" = some (.ptr K.b) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hnep1 : lookupName S1.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have henv1 : S1.env = cells [("%55", .int 32 sp9),
      ("%idxprom.le1291", .int 64 idx)] s.env := rfl
  have hbase1 : Stage2NoEventWalkBaseLookups K S1 := by
    intro n v hv
    rw [henv1]
    exact Stage2NoEventWalkBaseLookups.cellsOfNames
      (names := ["%55", "%idxprom.le1291"]) hbase rfl
      (by decide : (["%55", "%idxprom.le1291"] : List String).all
        (fun n => decide (n ∉ stage2NoEventWalkBaseNames)) = true) n v hv
  have halen1 : lookupName S1.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    rw [henv1, valueCells_notin (by
      show "%alen.0.ph1405" ∉ (["%55", "%idxprom.le1291"] : List String)
      decide)]
    exact halen
  have harena1 : lookupName S1.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    rw [henv1, valueCells_notin (by
      show "%arena.0.ph1406" ∉ (["%55", "%idxprom.le1291"] : List String)
      decide)]
    exact harena
  have hpos : (idx.signExtend 64).toNat < 2 ^ 63 := by
    have hlane : (BitVec.ofNat 32 lane).toNat < 2 ^ 32 := (BitVec.ofNat 32 lane).isLt
    simpa only [idx] using stage2NoEventLane_signExtend_lt hlane
  have hk1lt64 : k + 1 < 2 ^ 64 := by have := h.nepLt; omega
  have hguard : evalICmp .ult (BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 K.nep) = 1 :=
    value_ult_one hk1lt64 h.nepLt hknext
  let sE : State := stage2NoEventWalkNext
    (scalarCells S1.env (BitVec.ofNat 64 (k + 1)) idx bv sp9
      (BitVec.ofNat 64 K.terms) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.nep)
      (K.b + (idx.signExtend 64).toNat)) S1 "cond.true"
  have L2 : Stage2NoEventWalkLink calls K mem S1 K sE :=
    link_scalar_true (calls := calls) (K := K) (mem := mem)
      (inc := BitVec.ofNat 64 (k + 1)) (idx := idx) (bv := bv) (sp := sp9)
      (terms := BitVec.ofNat 64 K.terms) (tok := BitVec.ofNat 64 K.tok)
      (nep := BitVec.ofNat 64 K.nep) (b := K.b)
      L1.inv' hpc1 hpre1 hinc1 hidx1 hbv1 hsp1 htr1 htok1 hb1 hnep1 hpos hguard
  have hidxE : lookupName sE.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    have h0 : lookupName sE.env "%idxprom.lcssa" = some (.int 64 idx) := by
      simp only [sE, stage2NoEventWalkNext, scalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    simpa only [idx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlane32] using h0
  have harrE : lookupName sE.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)) := by
    have h0 : lookupName sE.env "%arrayidx6.le1046" =
        some (.ptr (K.b + (idx.signExtend 64).toNat)) := by
      simp only [sE, stage2NoEventWalkNext, scalarCells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have h1 : (idx.signExtend 64).toNat = lane := by
      rw [show idx = BitVec.ofNat 64 lane from by
        simp only [idx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlane32]]
      exact value_signExtend_lane hlane32
    rw [h1] at h0
    exact h0
  have hlcE : lookupName sE.env "%.lcssa" = some (.int 8 bv) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hincE : lookupName sE.env "%inc.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hspE : lookupName sE.env "%sp.0.lcssa1091.wide" =
      some (.int 32 sp9) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hfrE : lookupName sE.env "%frame.0.lcssa1097" = some (.int 8 1) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htrE : lookupName sE.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htokE : lookupName sE.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have henvE : sE.env = cells (scalarCells [] (BitVec.ofNat 64 (k + 1)) idx bv sp9
      (BitVec.ofNat 64 K.terms) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.nep)
      (K.b + (idx.signExtend 64).toNat)) S1.env := rfl
  have hbaseE : Stage2NoEventWalkBaseLookups K sE := by
    intro n v hv
    rw [henvE]
    exact Stage2NoEventWalkBaseLookups.cellsOfNames
      (names := ["%cmp436", "%arrayidx6.le1046", "%tokens.0.lcssa1073",
        "%terms.0.lcssa1079", "%sp.0.lcssa1091.wide", "%frame.0.lcssa1097",
        "%.lcssa", "%idxprom.lcssa", "%inc.lcssa"]) hbase1 rfl
      (by decide : (["%cmp436", "%arrayidx6.le1046", "%tokens.0.lcssa1073",
        "%terms.0.lcssa1079", "%sp.0.lcssa1091.wide", "%frame.0.lcssa1097",
        "%.lcssa", "%idxprom.lcssa", "%inc.lcssa"] : List String).all
          (fun n => decide (n ∉ stage2NoEventWalkBaseNames)) = true) n v hv
  have halenE : lookupName sE.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    rw [henvE, valueCells_notin (by
        show "%alen.0.ph1405" ∉ (["%cmp436", "%arrayidx6.le1046",
          "%tokens.0.lcssa1073", "%terms.0.lcssa1079", "%sp.0.lcssa1091.wide",
          "%frame.0.lcssa1097", "%.lcssa", "%idxprom.lcssa",
          "%inc.lcssa"] : List String)
        decide),
      henv1, valueCells_notin (by
        show "%alen.0.ph1405" ∉ (["%55", "%idxprom.le1291"] : List String)
        decide)]
    exact halen
  have harenaE : lookupName sE.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    rw [henvE, valueCells_notin (by
        show "%arena.0.ph1406" ∉ (["%cmp436", "%arrayidx6.le1046",
          "%tokens.0.lcssa1073", "%terms.0.lcssa1079", "%sp.0.lcssa1091.wide",
          "%frame.0.lcssa1097", "%.lcssa", "%idxprom.lcssa",
          "%inc.lcssa"] : List String)
        decide),
      henv1, valueCells_notin (by
        show "%arena.0.ph1406" ∉ (["%55", "%idxprom.le1291"] : List String)
        decide)]
    exact harena
  have hspE' : lookupName sE.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) := by
    simpa only [sp9] using hspE
  have p := stage2NoEventWalkValueProviderAt_condTrue (calls := calls)
    (K := K) (mem := mem) (s := sE) (k := k) (lane := lane)
    (sp := iv.toNat % 2 ^ 32) (bv := bv)
    (by simpa only [sE, stage2NoEventWalkNext] using L2.inv') rfl hent
    hknext hbPos hbaseE hidxE harrE hlcE hincE hspE' hfrE htrE htokE halenE harenaE
  have hrunHL : ∀ n, runFuel calls (2 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody sE := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2]
  exact { sE := sE, seg := ⟨hrunHL, L2.inv'⟩, prov := p }

/-! ### The provider at `scalar.loopexit`

The provider half of the class route, stated at the entry state: the entry head's
two links, the `cond.true` provider, and the entry's own lane and byte. -/

/-- **The value class's provider from `scalar.loopexit`** (the end test taken). -/
noncomputable def stage2NoEventWalkValueProv_of_entry_true {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k lane : Nat} {s : State}
    {iv : BitVec 64} {byte : UInt8}
    (hinv : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar.loopexit")
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (h8 : lookupName s.env "%8" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hinc : lookupName s.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hbv : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 byte.toNat)))
    (htr : lookupName s.env "%terms.0" = some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hent : K.ent[k]? = some lane) (hlane32 : lane < 2 ^ 32)
    (hknext : k + 1 < K.nep) (hbPos : 1 ≤ K.b)
    (hbs : K.bs[lane]? = some byte)
    (hread : readBytes s.mem (K.b + lane) 1 = some [byte])
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord))) :
    Stage2NoEventWalkValueProv calls mem K k s := by
  classical
  have hb : lookupName s.env "%b" = some (.ptr K.b) :=
    stage2NoEventWalkBase_b hbase
  have hnep : lookupName s.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    stage2NoEventWalkBase_nep hbase
  let E :=
    stage2NoEventWalkValueEntry_true (calls := calls) (K := K) (mem := mem)
      (s := s) (k := k) (lane := lane) (iv := iv) (bv := BitVec.ofNat 8 byte.toNat)
      hinv hpc hbase h8 hiv hinc hbv htr htok hb hnep halen harena hent hlane32
      hknext hbPos
  exact
    { e := E.prov.e
      j := 2 + E.prov.j
      q := E.prov.q
      cond := E.prov.cond
      lane := lane
      byte := byte
      sp := iv.toNat % 2 ^ 32
      fr := 1
      seg := E.seg.trans E.prov.seg
      regs := E.prov.regs
      laneLt := hlane32
      laneEq := hent
      byteEq := hbs
      read := hread
      laneLeQ := E.prov.laneLeQ
      qLeCond := E.prov.qLeCond
      condLeN := E.prov.condLeN
      qLt64 := E.prov.qLt64
      condLt63 := E.prov.condLt63
      provBound := by have := E.prov.bound; omega
      base := E.prov.base }

/-! ### The row

The value class's continuing row, from a provider at any state and the arm's own
route.  This is `stage2NoEventWalkValueRow_cont_of_route_count` at
`stage2NoEventWalkValueRoute_of_parts` — the head-free composition the four
per-arm wrappers of `JsonStage2NoEventWalkRowsValue` fill. -/

/-- **The value class's continuing row from a provider and an arm route.** -/
noncomputable def stage2NoEventWalkValueRow_of_prov {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (count : Stage2NoEventWalkCount K k)
    (prov : Stage2NoEventWalkValueProv calls mem K k s)
    (arm : Stage2NoEventWalkValueArmRoute calls mem K k prov.e)
    (hcredit : prov.j + arm.jarm +
      stage2NoEventWalkPotential arm.K' arm.knext ≤
        stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let route := stage2NoEventWalkValueRoute_of_parts prov arm
  refine stage2NoEventWalkValueRow_cont_of_route_count count route ?_
  exact hcredit

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkInv.laneWordAt
#print axioms stage2NoEventWalkBase_b
#print axioms stage2NoEventWalkBase_k219
#print axioms stage2NoEventWalkValueLand
#print axioms stage2NoEventWalkValueProviderAt_condTrue
#print axioms stage2NoEventWalkValueProviderAt_condEnd
#print axioms stage2NoEventWalkValueEntry_true
#print axioms stage2NoEventWalkValueProv_of_entry_true
#print axioms stage2NoEventWalkValueRow_of_prov

end LeanLLVM.Refinement
