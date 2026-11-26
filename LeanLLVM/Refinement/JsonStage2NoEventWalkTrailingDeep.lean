/-
The no-event walk's trailing exit at a live depth: the empty pair closes on the
document's last entry and the walk pops to the parent's `after_value`.

At depth zero `JsonStage2NoEventWalkRowsAfterValue`'s `stage2NoEventWalkBracketZeroRow`
/ `…BraceZeroRow` read the trailing entry as the terminal lane: `%cmp355` holds,
and `if.then357` accepts at `k + 2 = K.nep` or refuses below it.  At a live depth
neither applies.  The head's peeled dispatch stores one stack byte
(`if.then47.peel`/`if.then20`, the enclosing tag), reads the entry at `k + 1`, and
at `]`/`}` reaches `if.then334`/`if.then81` and `close_arr`/`close_obj`; the
closer's depth test at the popped word is then non-zero, so the walk takes
`if.then350`/`if.then343` (the pop of the tag it just stored) and lands on
`after_value` at `k + 2` with `%sp.4 = sp ≠ 0` and `%k.6 = k + 2`.

There `%cmp355 = 0`, so the dispatch takes `if.end369` and reads
`%cmp358 = (%k.6 < %nep)`, i.e. `k + 2 < K.nep`:

* **`k + 2 = K.nep`** — `%cmp358 = 0`, and `if.then372` stores the three zero
  words and `%n` at `%err`, `cleanup580` returns zero.  This is the trailing row
  at a live depth: a refusal, because the stack still holds the enclosing
  container when the entry stream runs out.  **Proved here**, both classes:
  `stage2NoEventWalkBracketTrailDeepRow` and `stage2NoEventWalkBraceTrailDeepRow`,
  with the shared `after_value → if.end369 → if.then372` dispatch and the terminal
  block's row `stage2NoEventWalkAfterValueRefuseRowOfEntry`.
* **`k + 3 = K.nep`** — `%cmp358 = 1` and the dispatch enters `if.end378`, where
  the parent reads the entry at `k + 2` as its own next byte and routes on the
  frame word.  That prefix is proved here as a segment
  (`stage2NoEventWalkAfterValueContinuePrefix`, two blocks to `if.end378`'s entry);
  the parent's element route **beyond that entry** is **not in this tree**: the
  composed element route (`stage2NoEventWalkCycle_of_afterValue`) needs
  `CycleSrc.klt = k + 3 < K.nep`, refuted here, and the spent-stream termination
  (`value.outer.backedge`'s false arm to `if.then`) is not composed; the same
  index's frame-zero (`if.then384`) and parent-closer (`if.end410`) arms are
  likewise unstated.
* **`k + 1 = K.nep`** — the closer at `k + 1` does not exist.  For the `[]` class
  the peeled dispatch's `if.end51.peel` sees `%inc.peel = k + 1 ≮ %nep` and
  refuses at `if.then321`; for `{}` the head's guard is `if.end23`
  (`%cmp66.not = (%inc.lcssa1129 ult %nep)`) and its refusal is `if.then68`.
  Both are the head's own refusal, before any pair route, and whose false-arm
  link is **not in this tree** (the committed `link_ifEnd51peel` and
  `link_ifEnd23` state their true arms only), so this module names the subcase
  rather than producing it.

**The route and its price.**  The `[]` pair is the eleven blocks of
`stage2NoEventWalkBracketPairAfterValue` (an existing denotation: the peeled
dispatch, the push, `if.end327.peel`'s `]` read, the count store, `close_arr` and
`if.then350`'s pop) at the pair's carry (`tok + 2`, `terms + 7`); the `{}` pair is
the thirteen blocks of `stage2NoEventWalkBraceTrailPairRoute` — the committed
`stage2NoEventWalkBracePairLeg`'s blocks at its trailing endpoint, exposed here
because the committed leg bundles its endpoint as a `CycleSrc` whose `klt` and
`comma` fields `k + 2 = K.nep` refutes.  Both routes then take the two dispatch
blocks and, on the refusal arm, the terminal block: fourteen and sixteen blocks.
They are payable because the trailing pair leaves two entries' allowance:
`stage2NoEventWalkPotential K k ≥ 32 · 2 = 64`, and the pair carry moves only
`tok`/`terms`, which the potential does not read (`…PairCarry_potential`, `rfl`).

**What the caller supplies.**  The push's staging (the post-push entry at `k + 1`
and its document byte, the popped stack byte, its length and — for `[]`, whose
committed endpoint bundle states it — its value), the reference-side evidence
`Stage2NoEventRun` at the route's memory (the push's one stack byte included) and
the parser's refusal `Stage2NoEventWalkReferenceRefuse`.  Nothing about the
parent's container beyond its depth and tag is read: the refusal arm queries only
`%sp.4`, `%k.6` and `%nep`.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkBracketParentCloser
import LeanLLVM.Refinement.JsonStage2NoEventWalkBraceFrameZeroPair
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsAfterValue
import LeanLLVM.Refinement.JsonStage2NoEventWalkTerminalA

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The dispatch at a live depth, refusal arm

`afterValue_denote` states the dispatch at `%sp.4 ≠ 0` and `%k.6 < %nep` — the
live edge.  The trailing case needs the other arm: the same `phi` run, then
`%cmp355 = 0` and `%cmp358 = 0`.  The cells differ only in the two test words. -/

/-- The refusal arm's two cells, newest first. -/
def afterValueRefuseDispatchCells : List (String × Value) :=
  [("%cmp358", .int 1 0), ("%cmp355", .int 1 0)]

/-- **The dispatch's two tests at a live depth and a spent entry stream.**  Same
instruction list as `afterValue_dispatch_denote`; `nep ≤ k` makes the second test
zero where that lemma's `k < nep` makes it one. -/
theorem stage2NoEventWalkAfterValueRefuse_dispatch_denote (calls : Calls) (env : Env)
    (s : State) {sp k nep : Nat}
    (hsp : lookupName env "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    (hkLt : k < 2 ^ 64) (hkle : nep ≤ k) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls afterValueDispatchInstrs (stateAt env s) =
      some (stateAt (cells afterValueRefuseDispatchCells env) s) := by
  rw [afterValueDispatchInstrs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%cmp355") (a := "%sp.4") (p := .eq) (w := 32)
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 0) ?_
    (is := [Instr.icmp "%cmp358" IPred.ult 64 (Operand.reg "%k.6")
      (Operand.reg "%nep")])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_eq_zero (x := BitVec.ofNat 32 sp)
    (c := BitVec.ofNat 32 0) (stage2NoEventOfNat32_ne hspLt hspNe)]
  rw [denoteCode_icmp_ult_reg (calls := calls)
    (env := ("%cmp355", Value.int 1 (0 : BitVec 1)) :: env) (s := s)
    (d := "%cmp358") (a := "%k.6") (b := "%nep")
    (x := BitVec.ofNat 64 k) (y := BitVec.ofNat 64 nep) ?_ ?_ (is := [])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_ult_zero (w := 64) (x := k) (y := nep) hkLt hnepLt
    (by omega)]
  simp only [afterValueRefuseDispatchCells, cells, denoteCode_nil]

/-- **The `after_value` block's run on its refusal arm**: the `phi` run and the
two tests, at `%sp.4 ≠ 0` and `%nep ≤ %k.6`. -/
theorem stage2NoEventWalkAfterValueRefuse_denote {calls : Calls} {env : Env}
    {s : State} {p : String} {fr sp k alen arena terms tok nep : Nat}
    (hpre : s.pre = some p)
    (hsel : PhiSelects (stateAt env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 tok))])
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    (hkLt : k < 2 ^ 64) (hkle : nep ≤ k) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls afterValueBlock.instrs (stateAt env s) =
      some (stateAt
        (cells afterValueRefuseDispatchCells (cells (afterValuePhiCells fr sp k alen
          arena terms tok) env)) s) := by
  have hphi := afterValue_phi_denote (calls := calls) (s := s) (env := env)
    (fr := fr) (sp := sp) (k := k) (alen := alen) (arena := arena) (terms := terms)
    (tok := tok) hpre hsel
  rw [afterValueBlock]
  rw [denoteCode_append_apply (a := afterValuePhiInstrs) (b := afterValueDispatchInstrs)
    (s := stateAt env s)
    (s' := stateAt (cells (afterValuePhiCells fr sp k alen arena terms tok) env) s)
    hphi (by decide)]
  rw [stage2NoEventWalkAfterValueRefuse_dispatch_denote (calls := calls)
    (env := cells (afterValuePhiCells fr sp k alen arena terms tok) env) (s := s)
    (sp := sp) (k := k) (nep := nep)
    (by
      exact cells_lookup_of_mem _ _ (by simp [afterValuePhiCells]) (by
        rw [show (afterValuePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide))
    (by
      exact cells_lookup_of_mem _ _ (by simp [afterValuePhiCells]) (by
        rw [show (afterValuePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide))
    (by
      rw [cells_lookup_of_notin _ _ (by
        rw [show (afterValuePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide)]
      exact hnep)
    hspLt hspNe hkLt hkle hnepLt]

/-! ### The refusal row at an after-value entry

The two dispatch blocks and the terminal block.  The entry carries the `phi`
run, the depth and the base lookups; the route's memory and the source's segment
come from the caller (the class route above), so the row is stated once and both
classes use it. -/

/-- **The trailing refusal row from an `after_value` entry.**  `h` is the head at
`k₀` with its trace; `e` is the entry the class route reaches at `k` (`= k₀ + 2`)
with `%sp.4 = e.sp ≠ 0` and `%nep ≤ k`; `hj` is the route's run.  The row is the
`if.end369` refusal (`if.then372`'s zero stores at `%n`), priced at the two
dispatch blocks plus the terminal block. -/
noncomputable def stage2NoEventWalkAfterValueRefuseRowOfEntry {gap : Calls}
    {mem : Mem} {F : Nat} {K K' : Stage2NoEventWalkCarry} {k₀ k : Nat} {s sE : State}
    {j : Nat}
    (h : Stage2NoEventWalkHead K mem k₀ s)
    (htrace : Stage2NoEventWalkTrace K)
    (e : Stage2NoEventWalkAfterValueEntry (stage2NoEventCalls gap) mem K' k sE)
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hbaseK : Stage2NoEventWalkBaseLookups K sE)
    (hk64 : k < 2 ^ 64)
    (hspNe : e.sp ≠ 0)
    (hkle : K.nep ≤ k)
    (hcost : j + 3 ≤ stage2NoEventWalkPotential K k₀ + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)))
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k₀ s := by
  classical
  refine Classical.choice ?_
  obtain ⟨pE, hpre, hsel⟩ := e.phiRun
  have hnep : lookupName sE.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    hbaseK "%nep" _ (by simp [stage2NoEventWalkBaseValues,
      stage2NoEventWalkParamEntries])
  have hnepLt : K.nep < 2 ^ 64 := h.inv.nepLt
  let e1 : Env := cells afterValueRefuseDispatchCells
    (cells (afterValuePhiCells e.frame e.sp k K'.arena.length K'.arenaWord
      K'.terms K'.tok) sE.env)
  let r1 : State := stage2NoEventWalkNext e1 sE "if.end369"
  let r2 : State := stage2NoEventWalkNext e1 r1 "if.then372"
  have l1 : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sE K' r1 :=
    stage2NoEventWalkLink_condbr_false e.inv (by rw [e.pc]; exact afterValueBlock_find)
      (stage2NoEventWalkAfterValueRefuse_denote (calls := stage2NoEventCalls gap)
        (env := sE.env) (s := sE) (p := pE) (fr := e.frame) (sp := e.sp) (k := k)
        (alen := K'.arena.length) (arena := K'.arenaWord) (terms := K'.terms)
        (tok := K'.tok) (nep := K.nep) hpre hsel hnep e.spLt hspNe hk64 hkle hnepLt)
      rfl (by cycle_lk)
  have l2 : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem r1 K' r2 :=
    stage2NoEventWalkLink_condbr_false l1.inv'
      (by rw [show r1.pc = "if.end369" from rfl]; exact ifEnd369Block_find)
      (by rw [ifEnd369Block]; exact denoteCode_nil (stage2NoEventCalls gap) (stateAt e1 r1))
      rfl (by cycle_lk)
  have hmem : r2.mem = sE.mem := by
    simp only [r2, r1, stage2NoEventWalkNext]
  have hbase1 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName (cells (afterValuePhiCells e.frame e.sp k K'.arena.length
        K'.arenaWord K'.terms K'.tok) sE.env) n = some v :=
    stage2NoEventCycleBase (K := K) hbaseK
      (cs := afterValuePhiCells e.frame e.sp k K'.arena.length K'.arenaWord
        K'.terms K'.tok)
      (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
        "%sp.4", "%frame.6"]) rfl (by decide)
  have hbase2 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName e1 n = some v :=
    stage2NoEventCycleBase (K := K) hbase1
      (cs := afterValueRefuseDispatchCells) (names := ["%cmp358", "%cmp355"])
      rfl (by decide)
  have hbase : Stage2NoEventWalkBaseLookups K r2 := hbase2
  have hpar : Stage2NoEventWalkParams K r2 :=
    stage2NoEventWalkBaseLookups_params hbase
  have hloc : Stage2NoEventWalkLocals K r2 :=
    stage2NoEventWalkBaseLookups_locals hbase h.inv.xjNext0
  have hw : lookupName r2.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hbase "%n" (.int 64 (BitVec.ofNat 64 K.n)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hle : (BitVec.ofNat 64 K.n).toNat ≤ K.n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  have hreport' : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem r2.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmem]; exact hreport
  have hj' : ∀ n, runFuel (stage2NoEventCalls gap) (j + 2 + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody r2 := by
    intro n
    rw [show j + 2 + n = j + (2 + n) from by omega, hj (2 + n),
      show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel l1 (1 + n),
      stage2NoEventWalkLink_runFuel l2 n]
  exact ⟨stage2NoEventZeroBlock_row (gap := gap) (F := F) (k := k₀)
    (sE := r2) (blk := "if.then372") (b := stage2NoEventIfThen372Block)
    (w := "%n") (x := BitVec.ofNat 64 K.n) h hj' rfl
    stage2NoEventIfThen372Block_find stage2NoEventIfThen372Block_instrs
    (by decide) (by decide) hpar hloc hw hle
    (by omega)
    hreport' htrace hrouteFrame hdata⟩

/-! ### The `[]` pair at a trailing endpoint

`stage2NoEventWalkBracketPairAfterValue` is the eleven-block route to
`after_value(k + 2)` with the endpoint entry and the push's memory exposed; it
takes `k + 2 ≤ K.nep`, which the trailing shape meets at equality. -/

/-- **The bracket trailing exit at a live depth, the last entry a `]`.**  The
`[]` pair closes at `k + 1`, the pop restores the parent's depth and tag, and
`after_value`'s refusal arm (its entry stream spent at `k + 2 = K.nep`) returns
zero. -/
noncomputable def stage2NoEventWalkBracketTrailDeepRow {gap : Calls} {mem : Mem}
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
    (hlast : k + 2 = K.nep)
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
    (hk63 : k + 3 < 2 ^ 63)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem
        (writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
          (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
        K.tokensOut K.valuesOut K.sumOut K.err (BitVec.ofNat 64 K.n)))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  classical
  refine Classical.choice ?_
  let P := stage2NoEventWalkBracketPairAfterValue (calls := stage2NoEventCalls gap)
    h htrace hk hbs hb hk1 hbs1 hb1 hspH hfrH h1H hspPos hspLe hspLt
    (by omega) hlaneW hval4lt hbyte1W hbytePop hbsLen hbsVal hk63
  have hpush := stage2NoEventWalkBracketPushAddr_eq K hspPos hspLt
  have hmemE : P.s'.mem = writeBytes s.mem (K.stk + (sp - 1))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    rw [P.memEq, hpush]
  have hspNe : P.entry.sp ≠ 0 := by rw [P.spEq]; omega
  have hreport' : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem P.s'.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmemE, ← hpush]; exact hreport
  have hrouteFrame : UnchangedOutside s.mem P.s'.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) := by
    rw [hmemE]
    refine UnchangedOutside.write_le (a := K.stk + (sp - 1)) (w := 1)
      (UnchangedOutside.refl' s.mem _) ⟨(K.stk, stage2NoEventStackExtent), ?_,
        by omega, ?_⟩ (by simp [natToBytes_length])
    · simp [stage2NoEventRunRegions, stage2NoEventStagedRegions]
    · simp only [stage2NoEventStackExtent]; omega
  have hpot : 64 ≤ stage2NoEventWalkPotential K k := by
    unfold stage2NoEventWalkPotential
    have hge : 2 ≤ K.nep - k := by omega
    have hmul : 32 * 2 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
    omega
  exact ⟨stage2NoEventWalkAfterValueRefuseRowOfEntry (gap := gap) (F := F)
    (k₀ := k) (j := 11) (K' := stage2NoEventWalkPairCarry K) h htrace P.entry
    P.seg.run P.entry.baseLookups (by omega) hspNe (by omega) (by omega)
    hreport' hrouteFrame hdata⟩

/-! ### The `{}` pair at a trailing endpoint

The committed brace leg (`stage2NoEventWalkBracePairLeg`) bundles its endpoint as
a `CycleSrc`: its `klt` field is `k + 2 < K.nep` and its `comma` field reads the
entry at `k + 2`, both of which `k + 2 = K.nep` refutes.  The thirteen blocks
themselves use neither, so they are re-stated here at the trailing endpoint, with
the entry returned as data. -/

/-- **The empty object pair at a trailing endpoint**: thirteen blocks from the
head at `{` to `after_value`'s entry at `k + 2`, at the pair's carry, with the
entry's depth the head's and its frame the popped byte. -/
structure Stage2NoEventWalkBraceTrailPair (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp fr : Nat) where
  /-- The endpoint's state. -/
  s' : State
  /-- The thirteen blocks, at the pair's carry. -/
  seg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkBracePairCarry K) s' 13
  /-- The push's write is the route's only memory change. -/
  memEq : s'.mem = writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
    (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
  /-- The `after_value` entry at `k + 2`. -/
  entry : Stage2NoEventWalkAfterValueEntry calls mem
    (stage2NoEventWalkBracePairCarry K) (k + 2) s'
  /-- Its depth is the head's. -/
  spEq : entry.sp = sp

/-- **The `{}` pair's thirteen blocks at a trailing endpoint**, the endpoint entry
as data.  Every block and link is the committed leg's
(`stage2NoEventWalkBracePrologue`, `link_nodeBlock21_false`, `link_leafBlock19_true`,
`link_ifThen81_of_bound`, `link_closeObj_live`, `link_ifThen343`). -/
noncomputable def stage2NoEventWalkBraceTrailPairRoute {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (bracePopAddr K sp) 1 = some bs)
    (hbsLen : bs.length = 1) :
    Stage2NoEventWalkBraceTrailPair calls mem K k s sp fr := by
  classical
  refine Classical.choice ?_
  let Kc : Stage2NoEventWalkCarry := stage2NoEventWalkBracePairCarry K
  let spv : BitVec 32 := BitVec.ofNat 32 sp
  let k64 : BitVec 64 := BitVec.ofNat 64 k
  let termsv : BitVec 64 := BitVec.ofNat 64 K.terms
  let tokv : BitVec 64 := BitVec.ofNat 64 K.tok
  obtain ⟨⟨S8, hseg8, hmem8, -, P⟩⟩ :=
    stage2NoEventWalkBracePrologue (calls := calls) h hk hbs hb
    hspH hfrH hspPos hspLe hspLt hkbound hk63 hlaneW hval4lt hbyte1W
  have hstk8 : lookupName S8.env "%stk" = some (.ptr K.stk) :=
    P.hbase "%stk" (.ptr K.stk) (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have h11_8 : lookupName S8.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    rw [stage2NoEventWalkBytesToNat_single]
    exact P.h11
  have h11slt : evalICmp .slt (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = (0 : BitVec 1) := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]
    decide
  let S9 := stage2NoEventWalkNext (("%Pivot22", .int 1 0) :: S8.env) S8 "LeafBlock19"
  have L9 : Stage2NoEventWalkLink calls K mem S8 K S9 :=
    link_nodeBlock21_false P.inv P.pc h11_8 h11slt
  have h11_9 : lookupName S9.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h11_8
  have h11eq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = (1 : BitVec 1) := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]
    decide
  let S10 := stage2NoEventWalkNext (("%SwitchLeaf20", .int 1 1) :: S9.env) S9 "if.then81"
  have L10 : Stage2NoEventWalkLink calls K mem S9 K S10 :=
    link_leafBlock19_true L9.inv' rfl h11_9 h11eq
  have hk10 : lookupName S10.env "%k.0.lcssa1086" = some (.int 64 k64) := by
    simp only [S10, S9, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.hk
  have htok10 : lookupName S10.env "%tokens.0.lcssa1074" = some (.int 64 tokv) := by
    simp only [S10, S9, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.htokPhi
  have htr10 : lookupName S10.env "%terms.0.lcssa1080" = some (.int 64 termsv) := by
    simp only [S10, S9, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.htermsPhi
  have hk64nat : k64.toNat = k := by
    simp only [k64, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  have hcount10 : Stage2NoEventWalkCount K k64.toNat := by
    rw [hk64nat]; exact P.count
  have hkb : k64.toNat + 2 ≤ K.nep := by rw [hk64nat]; omega
  let S11 := stage2NoEventWalkNext (ifThen81Out S10.env k64 tokv termsv) S10 "close_obj"
  have L11 : Stage2NoEventWalkLink calls K mem S10 Kc S11 :=
    link_ifThen81_of_bound L10.inv' rfl rfl hk10 htok10 htr10 hcount10 hkb
  let sp2 : BitVec 32 := spv + BitVec.ofNat 32 1
  have hsp11 : lookupName S11.env "%inc24" = some (.int 32 sp2) := by
    simp only [S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [P.hinc24]
    simp only [sp2, spv, stage2NoEventWalkOfNat_add]
  have hk4c11 : lookupName S11.env "%inc82"
      = some (.int 64 (k64 + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hterms11 : lookupName S11.env "%add85"
      = some (.int 64 (termsv + BitVec.ofNat 64 3)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    rw [lookupName_cons_self]
  have htoks11 : lookupName S11.env "%inc84"
      = some (.int 64 (tokv + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen11 : lookupName S11.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.halen
  have harena11 : lookupName S11.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.harena
  have hsp2nat : sp2.toNat = sp + 1 := by
    have h1 : spv.toNat = sp := by
      simp only [spv, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hspLt]
    simp only [sp2, BitVec.toNat_add, h1]
    rw [show (BitVec.ofNat 32 1 : BitVec 32).toNat = 1 from by decide,
      Nat.mod_eq_of_lt (by omega : sp + 1 < 2 ^ 32)]
  have hdecEq : (sp2 + BitVec.ofNat 32 4294967295).toNat = sp := by
    rw [BitVec.toNat_add, hsp2nat,
      show (BitVec.ofNat 32 4294967295 : BitVec 32).toNat = 4294967295 from by decide]
    have h2 : sp + 1 + 4294967295 = sp + 1 * 2 ^ 32 := by
      show sp + 1 + 4294967295 = sp + 1 * 4294967296
      omega
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hspLt]
  have hdecne : (sp2 + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
    rw [hdecEq]; omega
  let S12 := stage2NoEventWalkNext
    (cells (closeObjTail sp2 ++ braceCloseObjCells sp2
      (k64 + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (termsv + BitVec.ofNat 64 3)
      (tokv + BitVec.ofNat 64 2)) S11.env) S11 "if.then343"
  have L12 : Stage2NoEventWalkLink calls Kc mem S11 Kc S12 :=
    link_closeObj_live L11.inv' rfl rfl hsp11 hk4c11 halen11 harena11 hterms11 htoks11
      hdecne
  let a343 : Nat := bracePopAddr K sp
  have hsp12 : lookupName S12.env "%sp.2" = some (.int 32 sp2) := by
    simp only [S12, stage2NoEventWalkNext, closeObjTail, braceCloseObjCells, cells,
      List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hstk12 : lookupName S12.env "%stk" = some (.ptr K.stk) := by
    simp only [S12, S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells,
      closeObjTail, braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk8
  have ha343 : a343 = closeReadAddr K.stk
      (sp2 + BitVec.ofNat 32 4294967294).toNat := by
    simp only [a343, sp2, spv, bracePopAddr]
  have hbytePop' : readBytes S12.mem a343 1 = some bs := by
    have h12 : S12.mem = writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
        (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
      simp only [S12, S11, S10, S9, stage2NoEventWalkNext]
      exact hmem8
    rw [h12]
    exact hbytePop
  let S13 := stage2NoEventWalkNext
    (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells a343 ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
      S12.env) S12 "after_value"
  have L13 : Stage2NoEventWalkLink calls Kc mem S12 Kc S13 :=
    link_ifThen343 L12.inv' rfl hsp12 hstk12 hbytePop' ha343
  have hrun : ∀ n, runFuel calls (5 + n) stage2NoEventBody S8 =
      runFuel calls n stage2NoEventBody S13 := by
    intro n
    rw [show 5 + n = 1 + (1 + (1 + (1 + (1 + n)))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L9, stage2NoEventWalkLink_runFuel L10,
      stage2NoEventWalkLink_runFuel L11, stage2NoEventWalkLink_runFuel L12,
      stage2NoEventWalkLink_runFuel L13]
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc S13 13 :=
    hseg8.trans ⟨hrun, L13.inv'⟩
  have h49 : lookupName S13.env "%49"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [S13, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells,
      List.cons_append, List.nil_append]
    rw [lookupName_cons_self]
  have hdec13 : lookupName S13.env "%dec"
      = some (.int 32 (sp2 + BitVec.ofNat 32 4294967295)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk4c13 : lookupName S13.env "%k.4"
      = some (.int 64 (k64 + BitVec.ofNat 64 2)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen6 : lookupName S13.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harena8 : lookupName S13.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hterms6 : lookupName S13.env "%terms.6"
      = some (.int 64 (termsv + BitVec.ofNat 64 3)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htoks6 : lookupName S13.env "%tokens.6"
      = some (.int 64 (tokv + BitVec.ofNat 64 2)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hbase : Stage2NoEventWalkBaseLookups Kc S13 := by
    have b9 := stage2NoEventCycleBase (K := K) (env := S8.env) P.hbase
      (cs := [("%Pivot22", .int 1 0)]) (names := ["%Pivot22"]) rfl (by decide)
    have b10 := stage2NoEventCycleBase (K := K) b9
      (cs := [("%SwitchLeaf20", .int 1 1)]) (names := ["%SwitchLeaf20"]) rfl (by decide)
    have b11 := stage2NoEventCycleBase (K := K) b10
      (cs := [("%add85", .int 64 (termsv + BitVec.ofNat 64 3)),
        ("%inc84", .int 64 (tokv + BitVec.ofNat 64 2)),
        ("%inc82", .int 64 (k64 + BitVec.ofNat 64 2))])
      (names := ["%add85", "%inc84", "%inc82"]) rfl (by decide)
    have b12 := stage2NoEventCycleBase (K := K) b11
      (cs := closeObjTail sp2 ++ braceCloseObjCells sp2
        (k64 + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
        (BitVec.ofNat 64 K.arenaWord) (termsv + BitVec.ofNat 64 3)
        (tokv + BitVec.ofNat 64 2))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    have b13 := stage2NoEventCycleBase (K := K) b12
      (cs := ("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells a343 ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
      (names := ["%49", "%arrayidx346", "%idxprom345", "%sub344"])
      rfl (by decide)
    intro n v hv
    exact b13 n v hv
  have hbsOpen : K.bs[lane]? = some (0x7B : UInt8) := by
    have hy : byte = (0x7B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [hy] using hbs
  have hbsClose : K.bs[next]? = some (0x7D : UInt8) := by
    have hy : nextByte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
    simpa [hy] using hbs1
  have htrace' : Stage2NoEventWalkTrace Kc :=
    Stage2NoEventWalkTrace.emptyObject htrace hbsOpen hbsClose
  have hcountC : Stage2NoEventWalkCount Kc (k + 2) :=
    Stage2NoEventWalkCount.step (a := 2) (b := 2) h.count rfl rfl (by omega)
  have hspbv : sp2 + BitVec.ofNat 32 4294967295 = BitVec.ofNat 32 sp := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt, hdecEq]
  have hmem13 : S13.mem = writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    have h : S13.mem = S8.mem := rfl
    rw [h]; exact hmem8
  exact ⟨{ s' := S13
           seg := hseg
           memEq := hmem13
           entry :=
             { inv := L13.inv'
               pc := rfl
               sp := sp
               spLt := hspLt
               frame := bytesToNat bs
               frameLt := stage2NoEventWalkBytesToNat_lt hbsLen
               count := hcountC
               phiRun := by
                 refine ⟨"if.then343", rfl, ?_⟩
                 refine PhiSelects.cons (op := .reg "%49") (by decide) ?_
                   (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
                     (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
                       (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
                         (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
                           (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                             (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                               PhiSelects.nil))))))
                 all_goals
                   simp only [stage2NoEventWalkBracePairCarry, hspbv, stateAt,
                     evalOperand, h49, hdec13, hk4c13, halen6, harena8, hterms6,
                     htoks6, k64, termsv, tokv, stage2NoEventWalkOfNat_add,
                     BitVec.ofNat_toNat, BitVec.setWidth_eq]
               baseLookups := hbase
               bPos := h.bPos
               trace := htrace' }
           spEq := by rfl }⟩

/-- **The brace trailing exit at a live depth, the last entry a `}`.**  The `{}`
pair closes at `k + 1`, the pop restores the parent's depth and tag, and
`after_value`'s refusal arm (its entry stream spent at `k + 2 = K.nep`) returns
zero. -/
noncomputable def stage2NoEventWalkBraceTrailDeepRow {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hlast : k + 2 = K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (bracePopAddr K sp) 1 = some bs)
    (hbsLen : bs.length = 1)
    (hk63 : k + 3 < 2 ^ 63)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem
        (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
          (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
        K.tokensOut K.valuesOut K.sumOut K.err (BitVec.ofNat 64 K.n)))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  classical
  refine Classical.choice ?_
  have R := stage2NoEventWalkBraceTrailPairRoute (calls := stage2NoEventCalls gap)
    h htrace hk hbs hb hbs1 hb1 hspH hfrH hspPos hspLe hspLt (by omega) hk63
    hlaneW hval4lt hbyte1W hbytePop hbsLen
  have hpush := stage2NoEventWalkBracePushAddr_eq K hspPos hspLt
  have hmemE : R.s'.mem = writeBytes s.mem (K.stk + (sp - 1))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    rw [R.memEq, hpush]
  have hspNe : R.entry.sp ≠ 0 := by rw [R.spEq]; omega
  have hreport' : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem R.s'.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmemE, ← hpush]; exact hreport
  have hrouteFrame : UnchangedOutside s.mem R.s'.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) := by
    rw [hmemE]
    refine UnchangedOutside.write_le (a := K.stk + (sp - 1)) (w := 1)
      (UnchangedOutside.refl' s.mem _) ⟨(K.stk, stage2NoEventStackExtent), ?_,
        by omega, ?_⟩ (by simp [natToBytes_length])
    · simp [stage2NoEventRunRegions, stage2NoEventStagedRegions]
    · simp only [stage2NoEventStackExtent]; omega
  have hpot : 64 ≤ stage2NoEventWalkPotential K k := by
    unfold stage2NoEventWalkPotential
    have hge : 2 ≤ K.nep - k := by omega
    have hmul : 32 * 2 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
    omega
  exact ⟨stage2NoEventWalkAfterValueRefuseRowOfEntry (gap := gap) (F := F)
    (k₀ := k) (j := 13) (K' := stage2NoEventWalkBracePairCarry K) h htrace R.entry
    R.seg.run R.entry.baseLookups (by omega) hspNe (by omega) (by omega)
    hreport' hrouteFrame hdata⟩

/-! ### The continuation prefix at a live depth

When the entry stream has one entry left (`k + 2 < K.nep`, i.e. `nep = k + 3` under
the trailing bound), the dispatch takes `if.end378`, where the parent reads the
entry at `k + 2` as its own next byte.  The two blocks are stated here; the
parent's route from `if.end378` is not. -/

/-- **The live dispatch's two blocks**: from an `after_value` entry at a
non-zero depth with a live entry, to `if.end378`'s entry.  The next block reads
the entry at `k`'s lane and the document's byte there — the parent's next
byte — which this statement leaves to that route. -/
theorem stage2NoEventWalkAfterValueContinuePrefix {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {sE : State}
    (e : Stage2NoEventWalkAfterValueEntry calls mem K k sE)
    (hspNe : e.sp ≠ 0) (hklt : k < K.nep) :
    ∃ s', Stage2NoEventWalkSegment calls mem K sE K s' 2 ∧
      s'.pc = "if.end378" ∧ s'.pre = some "if.end369" ∧
      lookupName s'.env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName s'.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 e.sp)) ∧
      2 ≤ stage2NoEventWalkPotential K k := by
  obtain ⟨pE, hpre, hsel⟩ := e.phiRun
  have hnep : lookupName sE.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    e.baseLookups "%nep" _ (by simp [stage2NoEventWalkBaseValues,
      stage2NoEventWalkParamEntries])
  have hk64 : k < 2 ^ 64 := by have := e.inv.nepLt; omega
  let e1 : Env := cells afterValueDispatchCells
    (cells (afterValuePhiCells e.frame e.sp k K.arena.length K.arenaWord
      K.terms K.tok) sE.env)
  let r1 : State := stage2NoEventWalkNext e1 sE "if.end369"
  let r2 : State := stage2NoEventWalkNext e1 r1 "if.end378"
  have l1 : Stage2NoEventWalkLink calls K mem sE K r1 :=
    stage2NoEventWalkLink_condbr_false e.inv (by rw [e.pc]; exact afterValueBlock_find)
      (afterValue_denote (calls := calls) (env := sE.env) (s := sE) (p := pE)
        (fr := e.frame) (sp := e.sp) (k := k) (alen := K.arena.length)
        (arena := K.arenaWord) (terms := K.terms) (tok := K.tok) (nep := K.nep)
        hpre hsel hnep e.spLt hspNe hk64 hklt e.inv.nepLt)
      rfl (by cycle_lk)
  have l2 : Stage2NoEventWalkLink calls K mem r1 K r2 :=
    stage2NoEventWalkLink_condbr_true l1.inv'
      (by rw [show r1.pc = "if.end369" from rfl]; exact ifEnd369Block_find)
      (by rw [ifEnd369Block]; exact denoteCode_nil calls (stateAt e1 r1))
      rfl (by cycle_lk)
  have hrun : ∀ n, runFuel calls (2 + n) stage2NoEventBody sE =
      runFuel calls n stage2NoEventBody r2 := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel l1 (1 + n),
      stage2NoEventWalkLink_runFuel l2 n]
  have hk6 : lookupName r2.env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)) := by
    cycle_lk
  have hsp4 : lookupName r2.env "%sp.4"
      = some (.int 32 (BitVec.ofNat 32 e.sp)) := by
    cycle_lk
  have hpot : 2 ≤ stage2NoEventWalkPotential K k := by
    unfold stage2NoEventWalkPotential
    have hge : 1 ≤ K.nep - k := by omega
    have hmul : 32 * 1 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
    omega
  exact ⟨r2, ⟨hrun, l2.inv'⟩, rfl, rfl, hk6, hsp4, hpot⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkAfterValueRefuse_dispatch_denote
#print axioms stage2NoEventWalkAfterValueRefuse_denote
#print axioms stage2NoEventWalkAfterValueRefuseRowOfEntry
#print axioms stage2NoEventWalkBracketTrailDeepRow
#print axioms stage2NoEventWalkBraceTrailPairRoute
#print axioms stage2NoEventWalkBraceTrailDeepRow
#print axioms stage2NoEventWalkAfterValueContinuePrefix

end LeanLLVM.Refinement
