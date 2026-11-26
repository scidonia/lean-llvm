/-
The no-event walk's continuation at `k + 3 = K.nep`: the three arms after
`if.end378`'s entry, and the row two of them compose.

`JsonStage2NoEventWalkTrailingDeep` proves the trailing refusals at
`k + 2 = K.nep` and, for `k + 3 = K.nep`, only the two-block prefix
`stage2NoEventWalkAfterValueContinuePrefix` from an `after_value` entry at
`k` to `if.end378`'s entry at `%k.6 = k`.  Beyond that entry the parent reads
the entry at `k` as its own next byte (`if.end378` loads `%52`'s lane and
`%53`'s document byte) and routes on the two words:

* `%frame.6 = 0` — the parent is an object — takes `if.then384` →
  `NodeBlock35`; the byte `}` (`125`) takes `LeafBlock33` → `do.body391` →
  `close_obj` → `if.then343` → `after_value` at `k + 1` (the frame-zero close at
  `2 ≤ sp`, where `close_obj`'s `%dec = %sp.2 − 1` is non-zero and takes
  `if.then343`; the `sp = 1` arm goes straight to `after_value` and is not this
  route), and the byte
  `,` (`44`) takes `LeafBlock31` → `if.end409`, whose `%inc379 = k + 1` is not
  below `%nep` here, so `if.then105` refuses;
* `%frame.6 ≠ 0` — the parent is an array — takes `if.end410` → `NodeBlock41`;
  the byte `]` (`93`) takes `LeafBlock39` → `do.body417` → `close_arr` →
  `after_value` at `k + 1` (the parent-closer close), and the byte `,` (`44`)
  takes `LeafBlock37` → `value.outer.backedge`, whose `%cmp.not.peel` is
  `%inc379 <%nep` — zero at `k + 3 = K.nep` — so `if.then` refuses (the
  element route, whose element does not exist).

The committed cycle `stage2NoEventWalkCycle_of_afterValue` needs
`k + 1 < K.nep` at its own index, so at `k + 3 = K.nep` the element route has
no head to continue to; the three arms all end at a terminal, and every one of
them is inside the head's own three-entry allowance.

**What is proved here.**

* the element route's missing piece: `value.outer.backedge`'s guard at a spent
  stream (`outerBackedgeSpentTailCells`, `outerBackedgeSpent_tail_denote`,
  `outerBackedge_spent_leaf_denote`), the seven blocks from the pair's
  endpoint entry at `k + 2` to `if.then`'s entry (the parent's `,` at `k + 2`,
  `stage2NoEventWalkElementSpentArm`), and the refusal row over them
  (`stage2NoEventWalkBracketContinueElementRow`), the terminal block's own zero
  store;
* the parent-closer close as data with its memory: the nine blocks from the
  pair's endpoint entry to the `after_value` entry at `k + 3`
  (`stage2NoEventWalkParentCloserDeepPoint`), the endpoint's depth and the
  route's memory, and the refusal row over them
  (`stage2NoEventWalkBracketContinueDeepRow`);
* the frame-zero close's route at the same index, delegated to the committed
  entry-exposed arms (`stage2NoEventWalkFrameZeroCloseArm`), with the price;
* the price the two rows pay (`stage2NoEventWalkPotential_three`: the head's
  `Φ K k ≥ 96` at `k + 3 ≤ K.nep`, which covers the pair's eleven blocks, the
  arm's at most nine and the terminal's three), and the reason no arm can be
  priced *from* `Φ K (k + 2)`: `Φ` is not monotone across the last entry
  (`stage2NoEventWalkPotential_atNep`, `Stage2NoEventWalkPotentialLastJump`),
  because `K.ent.getD` defaults to zero past the end.

**What is not proved, and why.**  The frame-zero close's *row* needs the
endpoint's memory equation (`s'.mem = s.mem`) so the refusal's report — a
reference-side supply stated at the terminal memory — can be read at the arm's
endpoint.  `stage2NoEventWalkFrameZeroBraceDeepEntry` exposes the endpoint
state, the entry, and the entry's depth and frame as data, but not the route's
memory: the committed arm's blocks write nothing, yet the statement does not say
so, and no lemma recovers it from an existential.  The route is therefore
stated here (the arm) and its row is one nine-block re-proof away, not a missing
route.  At `%sp.4 = 1` the two closers land at depth zero, which is the
acceptance lane (`stage2NoEventWalkBracketZeroTerminal`'s supply: the caller's
reference acceptance, report and boundary at the arm's carry), not this
module's.

**What the tree does not have at this index.**  The mismatched closers (a `}`
under an array parent, a `]` under an object parent) take `if.then428`/`if.then402`,
and the object parent's trailing `,` takes `if.then105`: three refusals whose
blocks are pinned (`stage2NoEventIfThen105Block`, `…402Block`, `…428Block`) but
whose routes are not composed here.  They are refusals at the same index, not
continuations.

The premises each statement takes are labelled where they are declared: the
pair's endpoint entry and its segment are the class lane's; the bytes, the lanes
and the pop are the caller's staging of the document and the stack; the
reference run's report, the route's frame and the refusal's `obs`/`toks` and
parser verdict are the deployment boundary's, exactly as the committed trailing
rows take them.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkTrailingDeep
import LeanLLVM.Refinement.JsonStage2NoEventWalkBraceCloseEntry
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsParentCloser

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_one readBytes_length)
open LeanLLVM.Refinement.BlockEval

/-! ### `value.outer.backedge` at a spent entry stream

The committed tail (`outerBackedgeTailCells`) pins `%cmp.not.peel = 1`, i.e.
`%k.0.ph.be < %nep`.  The element route at `k + 3 = K.nep` reads
`%k.0.ph.be = %inc379 = k + 3 = K.nep`, so its guard is zero and the block's
false arm is `if.then` — the trailing refusal.  These are that arm's cells and
its run; nothing about a block is restated. -/

/-- The backedge's tail cells at a spent stream: the guard is zero. -/
def outerBackedgeSpentTailCells (sp _k : Nat) : List (String × Value) :=
  [("%cmp.not.peel", .int 1 0),
   ("%wide.trip.count", .int 64 (BitVec.ofNat 64 (max sp 520))),
   ("%umax", .int 32 (BitVec.ofNat 32 (max sp 520))),
   ("%umax.max", .int 1 (if 520 < sp then 1 else 0)),
   ("%45", .int 64 (BitVec.ofNat 64 sp))]

/-- **The backedge's five computed cells at a spent stream**, the guard zero
because `%nep ≤ %k.0.ph.be`.  The same instruction list as
`outerBackedge_tail_denote`; only the `ult` test's value differs. -/
theorem outerBackedgeSpent_tail_denote (calls : Calls) (env : Env) (s : State)
    {sp k nep : Nat}
    (hsp : lookupName env "%sp.0.ph.be" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%k.0.ph.be" = some (.int 64 (BitVec.ofNat 64 k)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hk64 : k < 2 ^ 64) (hspent : nep ≤ k)
    (hnepLt : nep < 2 ^ 64) :
    denoteCode calls outerBackedgeTailInstrs (stateAt env s) =
      some (stateAt (cells (outerBackedgeSpentTailCells sp k) env) s) := by
  rw [outerBackedgeTailInstrs]
  rw [denoteCode_zext (calls := calls) (env := env) (s := s) (d := "%45")
    (v := "%sp.0.ph.be") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 sp) ?_
    (is := [Instr.icmp "%umax.max" IPred.ugt 32 (Operand.reg "%sp.0.ph.be")
        (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.select "%umax" (Ty.int 32) (Operand.reg "%umax.max")
        (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 hspLt]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env) (s := s)
    (d := "%umax.max") (a := "%sp.0.ph.be") (p := .ugt) (w := 32)
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 520) ?_
    (is := [Instr.select "%umax" (Ty.int 32) (Operand.reg "%umax.max")
        (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  have hugt : evalICmp .ugt (BitVec.ofNat 32 sp) (BitVec.ofNat 32 520) =
      (if 520 < sp then (1 : BitVec 1) else 0) := by
    by_cases h : 520 < sp
    · rw [ite_eq_left h]
      exact stage2NoEventICmp_ugt_one hspLt (by decide) h
    · rw [ite_eq_right h]
      exact stage2NoEventICmp_ugt_zero hspLt (by decide) (by omega)
  rw [hugt]
  rw [stage2NoEventDenoteSelect32 (calls := calls)
    (env := ("%umax.max", Value.int 1 (if 520 < sp then (1 : BitVec 1) else 0)) ::
      ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env) (s := s)
    (d := "%umax") (c := "%umax.max") (a := "%sp.0.ph.be")
    (bb := (if 520 < sp then (1 : BitVec 1) else 0)) (x := BitVec.ofNat 32 sp)
    (y := BitVec.ofNat 32 520) ?_ ?_
    (is := [Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  have hmax : (if (if 520 < sp then (1 : BitVec 1) else 0) = 1 then
      BitVec.ofNat 32 sp else BitVec.ofNat 32 520) =
      BitVec.ofNat 32 (max sp 520) := by
    by_cases h : 520 < sp
    · rw [ite_eq_left h, ite_eq_left rfl, Nat.max_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by decide), Nat.max_eq_right (by omega)]
  rw [hmax]
  rw [denoteCode_zext (calls := calls)
    (env := ("%umax", Value.int 32 (BitVec.ofNat 32 (max sp 520))) ::
      ("%umax.max", Value.int 1 (if 520 < sp then (1 : BitVec 1) else 0)) ::
      ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env)
    (s := s) (d := "%wide.trip.count")
    (v := "%umax") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 (max sp 520)) ?_
    (is := [Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 (by omega)]
  rw [denoteCode_icmp_ult_reg (calls := calls)
    (env := ("%wide.trip.count", Value.int 64 (BitVec.ofNat 64 (max sp 520))) ::
      ("%umax", Value.int 32 (BitVec.ofNat 32 (max sp 520))) ::
      ("%umax.max", Value.int 1 (if 520 < sp then (1 : BitVec 1) else 0)) ::
      ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env) (s := s)
    (d := "%cmp.not.peel") (a := "%k.0.ph.be") (b := "%nep")
    (x := BitVec.ofNat 64 k) (y := BitVec.ofNat 64 nep) ?_ ?_ (is := [])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_ult_zero (w := 64) (x := k) (y := nep) hk64 hnepLt
    (by omega)]
  simp only [outerBackedgeSpentTailCells, cells, denoteCode_nil]

/-- **`value.outer.backedge`'s run at `LeafBlock37`'s edge, spent stream**: its
`phi` run at the edge and the five computed cells with the guard zero. -/
theorem outerBackedge_spent_leaf_denote {calls : Calls} {env : Env} {s : State}
    {fr sp k alen arena terms tok nep : Nat}
    (hpre : s.pre = some "LeafBlock37")
    (hframe : lookupName env "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspc : lookupName env "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkc : lookupName env "%inc379" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName env "%alen.8" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.10" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName env "%terms.8" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 tok)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hk64 : k < 2 ^ 64) (hspent : nep ≤ k)
    (hnepLt : nep < 2 ^ 64) :
    denoteCode calls outerBackedgeBlock.instrs (stateAt env s) =
      some (stateAt
        (cells (outerBackedgeSpentTailCells sp k)
          (cells (outerBackedgePhiCells fr sp k alen arena terms tok) env)) s) := by
  have hphi := outerBackedge_phi_leaf_denote (calls := calls) (env := env) (s := s)
    (fr := fr) (sp := sp) (k := k) (alen := alen) (arena := arena) (terms := terms)
    (tok := tok) hpre hframe hspc hkc halen harena hterms htok
  rw [outerBackedgeBlock]
  rw [denoteCode_append_apply (a := outerBackedgePhiInstrs)
    (b := outerBackedgeTailInstrs) (s := stateAt env s)
    (s' := stateAt (cells (outerBackedgePhiCells fr sp k alen arena terms tok) env) s)
    hphi (by decide)]
  rw [outerBackedgeSpent_tail_denote (calls := calls)
    (env := cells (outerBackedgePhiCells fr sp k alen arena terms tok) env) (s := s)
    (sp := sp) (k := k) (nep := nep)
    (by
      exact cells_lookup_of_mem _ _ (by simp [outerBackedgePhiCells]) (by
        rw [show (outerBackedgePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide))
    (by
      exact cells_lookup_of_mem _ _ (by simp [outerBackedgePhiCells]) (by
        rw [show (outerBackedgePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide))
    (by
      rw [cells_lookup_of_notin _ _ (by
        rw [show (outerBackedgePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide)]
      exact hnep)
    hspLt hk64 hspent hnepLt]

/-! ### The element route at `k + 3 = K.nep`

The parent's `,` at `k + 2`: `after_value` → `if.end369` → `if.end378` →
`if.end410` → `NodeBlock41` → `LeafBlock37` → `value.outer.backedge`, whose
guard is zero, so the seventh block's false arm lands at `if.then`.  Seven
blocks, inside one entry's allowance. -/

/-- **The element route's endpoint as data**: the terminal block's entry at
`if.then`, the seven-block segment, the guard's zero, and the route's memory. -/
structure Stage2NoEventWalkElementPoint (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (s : State) where
  /-- The terminal block's entry. -/
  s' : State
  /-- The seven blocks. -/
  seg : Stage2NoEventWalkSegment calls mem K s K s' 7
  pc : s'.pc = "if.then"
  pre : s'.pre = some "value.outer.backedge"
  /-- The backedge's guard, zero at a spent stream. -/
  cmp : lookupName s'.env "%cmp.not.peel" = some (.int 1 0)
  /-- The route writes no memory. -/
  memEq : s'.mem = s.mem
  /-- The entry chain's live-ins survived the route. -/
  base : Stage2NoEventWalkBaseLookups K s'

/-- **The element route at a spent stream**: seven blocks from the pair's
`after_value` entry at `k + 2` (its parent an array, its next byte the `,`) to
`if.then`'s entry, with the backedge's guard zero.

The entry (`e`), its frame and depth, the comma at `k + 2`, and the bounds are
the caller's staging of the class route and the document; the entry stream's
length is the invariant's. -/
noncomputable def stage2NoEventWalkElementSpentArm {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (e : Stage2NoEventWalkAfterValueEntry calls mem K (k + 2) s)
    (hframeNe : e.frame ≠ 0) (hspNe : e.sp ≠ 0)
    (hcomma : ∀ lane, K.ent[k + 2]? = some lane → K.bs.getD lane 0 = 44)
    (hknep : K.nep = k + 3) (hk63 : k + 3 < 2 ^ 63) :
    Stage2NoEventWalkElementPoint calls mem K s := by
  classical
  refine Classical.choice ?_
  obtain ⟨pEdge, hpre, hsel⟩ := e.phiRun
  have hnep : lookupName s.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    e.baseLookups "%nep" _ (by simp [stage2NoEventWalkBaseValues,
      stage2NoEventWalkParamEntries])
  have hk64 : k + 2 < 2 ^ 64 := by have := e.inv.nepLt; omega
  have hklt' : k + 2 < K.nep := by omega
  -- the entry at `k + 2`, its lane's four bytes, and the document's byte
  have hlanes : readLanes32 s.mem K.ep K.nep = some K.ent :=
    e.inv.readLanes_off (stage2NoEventCycleOutLane e.inv) e.inv.entries
  obtain ⟨laneAV, bsAV, hgetAV, hreadAV, hvalAV, hltAV⟩ :=
    stage2NoEventCycleEnt_lane hlanes hklt'
  have hinsAV : laneAV < K.n := e.inv.inside laneAV (List.mem_of_getElem? hgetAV)
  have hdocAV : readBytes s.mem (K.b + laneAV) 1 = some [K.bs.getD laneAV 0] :=
    e.inv.readBytes_off (K := K) (a := K.b + laneAV) (N := 1)
      (bs := [K.bs.getD laneAV 0]) (stage2NoEventCycleOutDoc e.inv hinsAV) (by
        rw [readBytes_one, readByte_of_readBytes e.inv.doc hinsAV]
        rfl)
  have hcommaAV : K.bs.getD laneAV 0 = 44 := hcomma laneAV hgetAV
  have hbyteAV : readBytes s.mem (K.b + laneAV) 1 = some [44] := by
    rw [hcommaAV] at hdocAV
    exact hdocAV
  -- the chain's states
  let e1 : Env := cells afterValueDispatchCells
    (cells (afterValuePhiCells e.frame e.sp (k + 2) K.arena.length K.arenaWord
      K.terms K.tok) s.env)
  let r1 : State := stage2NoEventWalkNext e1 s "if.end369"
  let r2 : State := stage2NoEventWalkNext e1 r1 "if.end378"
  let e3 : Env := cells (ifEnd378Cells K.ep K.b laneAV (k + 2) e.frame 44) e1
  let r3 : State := stage2NoEventWalkNext e3 r2 "if.end410"
  let r4 : State := stage2NoEventWalkNext e3 r3 "NodeBlock41"
  let e5 : Env := cells nodeBlock41Cells e3
  let r5 : State := stage2NoEventWalkNext e5 r4 "LeafBlock37"
  let e6 : Env := cells leafBlock37Cells e5
  let r6 : State := stage2NoEventWalkNext e6 r5 "value.outer.backedge"
  let e7 : Env := cells (outerBackedgeSpentTailCells e.sp (k + 3))
    (cells (outerBackedgePhiCells e.frame e.sp (k + 3) K.arena.length K.arenaWord
      K.terms K.tok) e6)
  let r7 : State := stage2NoEventWalkNext e7 r6 "if.then"
  -- the after-value dispatch, its `ult` test one at `k + 2 < K.nep`
  have l1 : Stage2NoEventWalkLink calls K mem s K r1 :=
    stage2NoEventWalkLink_condbr_false e.inv (by rw [e.pc]; exact afterValueBlock_find)
      (afterValue_denote (calls := calls) (env := s.env) (s := s) (p := pEdge)
        (fr := e.frame) (sp := e.sp) (k := k + 2) (alen := K.arena.length)
        (arena := K.arenaWord) (terms := K.terms) (tok := K.tok) (nep := K.nep)
        hpre hsel hnep e.spLt hspNe hk64 hklt' e.inv.nepLt)
      rfl (by cycle_lk)
  have l2 : Stage2NoEventWalkLink calls K mem r1 K r2 :=
    stage2NoEventWalkLink_condbr_true l1.inv'
      (by rw [show r1.pc = "if.end369" from rfl]; exact ifEnd369Block_find)
      (by rw [ifEnd369Block]; exact denoteCode_nil calls (stateAt e1 r1))
      rfl (by cycle_lk)
  -- `if.end378` at the non-zero frame word and the `,`
  have l3 : Stage2NoEventWalkLink calls K mem r2 K r3 :=
    stage2NoEventWalkLink_condbr_false l2.inv'
      (by rw [show r2.pc = "if.end378" from rfl]; exact ifEnd378Block_find)
      (ifEnd378_denote (calls := calls) (env := e1) (s := r2)
        (ep := K.ep) (b := K.b) (lane := laneAV) (k := k + 2) (fr := e.frame)
        (byte := 44) (bs4 := bsAV)
        (by cycle_lk)
        (by exact e.baseLookups "%ep" _ (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
        (by exact e.baseLookups "%b" _ (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
        (by cycle_lk) (by omega) e.frameLt hframeNe hvalAV hltAV hreadAV hbyteAV)
      rfl (by cycle_lk)
  have l4 : Stage2NoEventWalkLink calls K mem r3 K r4 :=
    stage2NoEventWalkLink_br l3.inv'
      (by rw [show r3.pc = "if.end410" from rfl]; exact ifEnd410Block_find)
      (by rw [ifEnd410Block]; exact denoteCode_nil calls (stateAt e3 r3))
      rfl
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_true l4.inv'
      (by rw [show r4.pc = "NodeBlock41" from rfl]; exact nodeBlock41Block_find)
      (nodeBlock41_denote (calls := calls) (env := e3) (s := r4) (by cycle_lk))
      rfl (by cycle_lk)
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock37" from rfl]; exact leafBlock37Block_find)
      (leafBlock37_denote (calls := calls) (env := e5) (s := r5) (by cycle_lk))
      rfl (by cycle_lk)
  -- the backedge's cells at `LeafBlock37`'s edge
  have hframe6 : lookupName e6 "%frame.6" = some (.int 8 (BitVec.ofNat 8 e.frame)) := by
    cycle_lk
  have hsp4 : lookupName e6 "%sp.4" = some (.int 32 (BitVec.ofNat 32 e.sp)) := by
    cycle_lk
  have hinc379 : lookupName e6 "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 3))) := by
    cycle_lk
  have halen8 : lookupName e6 "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    cycle_lk
  have harena10 : lookupName e6 "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    cycle_lk
  have hterms8 : lookupName e6 "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    cycle_lk
  have htokens8 : lookupName e6 "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    cycle_lk
  have hnep6 : lookupName e6 "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    cycle_lk
  -- the backedge's guard is zero at `%k.0.ph.be = k + 3 = %nep`
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_condbr_false l6.inv'
      (by rw [show r6.pc = "value.outer.backedge" from rfl]
          exact outerBackedgeBlock_find)
      (outerBackedge_spent_leaf_denote (calls := calls) (env := e6) (s := r6)
        (fr := e.frame) (sp := e.sp) (k := k + 3) (alen := K.arena.length)
        (arena := K.arenaWord) (terms := K.terms) (tok := K.tok) (nep := K.nep)
        rfl hframe6 hsp4 hinc379 halen8 harena10 hterms8 htokens8 hnep6
        e.spLt (by omega) (by omega) e.inv.nepLt)
      rfl (by cycle_lk)
  -- the base lookups through the seven layers
  have hbase7 : Stage2NoEventWalkBaseLookups K r7 := by
    have h1 := stage2NoEventCycleBase (K := K) (env := s.env) e.baseLookups
      (cs := afterValuePhiCells e.frame e.sp (k + 2) K.arena.length K.arenaWord
        K.terms K.tok)
      (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
        "%sp.4", "%frame.6"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := afterValueDispatchCells) (names := ["%cmp358", "%cmp355"])
      rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := ifEnd378Cells K.ep K.b laneAV (k + 2) e.frame 44)
      (names := ["%53", "%arrayidx386", "%idxprom385", "%cmp382", "%52",
        "%arrayidx380", "%inc379"]) rfl (by decide)
    have h4 := stage2NoEventCycleBase (K := K) h3
      (cs := nodeBlock41Cells) (names := ["%Pivot42"]) rfl (by decide)
    have h5 := stage2NoEventCycleBase (K := K) h4
      (cs := leafBlock37Cells) (names := ["%SwitchLeaf38"]) rfl (by decide)
    have h6 := stage2NoEventCycleBase (K := K) h5
      (cs := outerBackedgePhiCells e.frame e.sp (k + 3) K.arena.length
        K.arenaWord K.terms K.tok)
      (names := ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be",
        "%alen.0.ph.be", "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"])
      rfl (by decide)
    have h7 := stage2NoEventCycleBase (K := K) h6
      (cs := outerBackedgeSpentTailCells e.sp (k + 3))
      (names := ["%cmp.not.peel", "%wide.trip.count", "%umax", "%umax.max",
        "%45"]) rfl (by decide)
    exact h7
  have hrun : ∀ n, runFuel calls (7 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody r7 := by
    intro n
    rw [show 7 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + n)))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel l1, stage2NoEventWalkLink_runFuel l2,
      stage2NoEventWalkLink_runFuel l3, stage2NoEventWalkLink_runFuel l4,
      stage2NoEventWalkLink_runFuel l5, stage2NoEventWalkLink_runFuel l6,
      stage2NoEventWalkLink_runFuel l7]
  have hcmp7 : lookupName e7 "%cmp.not.peel" = some (.int 1 0) := by
    simp only [e7, outerBackedgeSpentTailCells, cells, lookupName_cons_self]
  exact ⟨⟨r7, ⟨hrun, l7.inv'⟩, rfl, rfl, hcmp7, rfl, hbase7⟩⟩

/-! ### The parent-closer close at `k + 3 = K.nep`

The parent's `]` at `k + 2`, at a nested depth: `ParentSepToCloseArr`'s seven
blocks to `close_arr`, its false test at `%sp.4 - 1 ≠ 0` to `if.then350`, and
the pop to `after_value` at `k + 3`.  Nine blocks; the endpoint's depth is
`%sp.4 - 1 ≠ 0` and the route writes no memory. -/

/-- **The parent-closer's endpoint as data**: the `after_value` entry at
`k + 3`, the nine-block segment, the source's memory, and the endpoint's depth
non-zero. -/
structure Stage2NoEventWalkParentCloserPoint (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The endpoint's state. -/
  s' : State
  /-- The `after_value` entry at `k + 3`, at the closer's carry. -/
  entry : Stage2NoEventWalkAfterValueEntry calls mem
    (stage2NoEventWalkCloserCarry K 4) (k + 3) s'
  /-- The nine blocks. -/
  seg : Stage2NoEventWalkSegment calls mem K s
    (stage2NoEventWalkCloserCarry K 4) s' 9
  /-- The route writes no memory. -/
  memEq : s'.mem = s.mem
  /-- The endpoint's depth, one lower than the source's. -/
  spNe : entry.sp ≠ 0

/-- **The parent-closer close as data**: nine blocks from the pair's
`after_value` entry at `k + 2` to the `after_value` entry at `k + 3`, at the
closer's carry, with the endpoint's depth non-zero and the route's memory the
source's.

The entry, the separator `]` at `k + 2`, and the pop at the endpoint's memory
are the caller's staging; the endpoint's frame word is the popped tag and is not
assumed. -/
noncomputable def stage2NoEventWalkParentCloserDeepPoint {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (e : Stage2NoEventWalkAfterValueEntry calls mem K (k + 2) s)
    (hframeNe : e.frame ≠ 0) (hspTwo : 2 ≤ e.sp)
    (hsep : Stage2NoEventWalkParentSep K k 93)
    (hknep : K.nep = k + 3) (hk63 : k + 3 < 2 ^ 63)
    {a : Nat} {bsP : List UInt8}
    (hpop : readBytes s.mem a 1 = some bsP)
    (hpopAddr : a = closeReadAddr K.stk
      ((BitVec.ofNat 32 e.sp + BitVec.ofNat 32 4294967295) +
        BitVec.ofNat 32 4294967295).toNat)
    (hbsLen : bsP.length = 1) :
    Stage2NoEventWalkParentCloserPoint calls mem K k s := by
  classical
  refine Classical.choice ?_
  obtain ⟨s7, lane, hseg7, hpc7, hpre7, hinv7, hmem7, hframe7, h54_7, hinc7,
    halen7, harena7, hterms7, htoks7, hbase7, hget, hbsClose⟩ :=
    stage2NoEventWalkParentSepToCloseArr e hframeNe (by omega) hsep
      (by omega) (by omega)
  have hspLt := e.spLt
  have hdec : (BitVec.ofNat 32 e.sp + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
    rw [stage2NoEventWalkOfNat32_dec e.sp (by omega) hspLt]
    omega
  let sp3 : BitVec 32 := BitVec.ofNat 32 e.sp + BitVec.ofNat 32 4294967295
  let frame8 : BitVec 8 := BitVec.ofNat 8 e.frame
  let r8 : State := parentSepArrState s7 frame8 sp3
    (BitVec.ofNat 64 (k + 2 + 1)) (BitVec.ofNat 64 K.arena.length)
    (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)
    (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
  have h54_7' : lookupName s7.env "%54" = some (.int 32 sp3) := h54_7
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloserCarry K 4) mem s7
      (stage2NoEventWalkCloserCarry K 4) r8 :=
    link_closeArr_doBody417_live (K := stage2NoEventWalkCloserCarry K 4)
      hinv7 hpc7 hpre7 hframe7 h54_7' hinc7 halen7 harena7 hterms7 htoks7 hdec
  have hsp3_8 : lookupName r8.env "%sp.3" = some (.int 32 sp3) := by
    simp only [r8, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hbase8 : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkCloserCarry K 4) r8 := by
    exact stage2NoEventCycleBase (K := K) (env := s7.env) hbase7
      (cs := parentSepArrCells frame8 sp3 (BitVec.ofNat 64 (k + 2 + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool349.not", "%tokens.7", "%terms.7", "%arena.9",
        "%alen.7", "%k.5", "%sp.3", "%frame.4"]) rfl (by decide)
  have hstk8 : lookupName r8.env "%stk" = some (.ptr K.stk) :=
    hbase8 "%stk" _ (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries,
        stage2NoEventWalkCloserCarry])
  have hr8mem : r8.mem = s.mem := by
    have h1 : r8.mem = s7.mem := rfl
    rw [h1, hmem7]
  have hpop8 : readBytes r8.mem a 1 = some bsP := by
    rw [hr8mem]
    exact hpop
  let r9 : State := bracketRead r8 sp3 a bsP
  have l9 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloserCarry K 4) mem r8
      (stage2NoEventWalkCloserCarry K 4) r9 :=
    link_ifThen350 (K := stage2NoEventWalkCloserCarry K 4) l8.inv' rfl hsp3_8
      hstk8 hpop8 hpopAddr
  have hrun : ∀ n, runFuel calls (2 + n) stage2NoEventBody s7 =
      runFuel calls n stage2NoEventBody r9 := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel l8, stage2NoEventWalkLink_runFuel l9]
  -- the entry's cells at the `if.then350` edge
  have h50 : lookupName r9.env "%50" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bsP))) := by
    simp only [r9, bracketRead, cells, stage2NoEventWalkNext]
    cycle_lk
  have hsp3_9 : lookupName r9.env "%sp.3" = some (.int 32 sp3) := by
    simp only [r9, bracketRead, cells, stage2NoEventWalkNext]
    cycle_lk
  have hk5_9 : lookupName r9.env "%k.5" =
      some (.int 64 (BitVec.ofNat 64 (k + 2 + 1))) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have halen9 : lookupName r9.env "%alen.7" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have harena9 : lookupName r9.env "%arena.9" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hterms9 : lookupName r9.env "%terms.7" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have htoks9 : lookupName r9.env "%tokens.7" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hbase9 : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkCloserCarry K 4) r9 := by
    exact stage2NoEventCycleBase (K := K) (env := r8.env) hbase8
      (cs := ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bsP))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295))
      (names := (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bsP))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295)).map
          (·.1)) rfl
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)
  have htrace9 : Stage2NoEventWalkTrace (stage2NoEventWalkCloserCarry K 4) :=
    Stage2NoEventWalkTrace.closeArray e.trace hbsClose
  have hsel9 : PhiSelects (stateAt r9.env r9) "if.then350" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 (bytesToNat bsP))),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp3.toNat)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 2 + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkCloserCarry K 4).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkCloserCarry K 4).tok))] := by
    refine PhiSelects.cons (op := .reg "%50") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, h50, hsp3_9, hk5_9, halen9, harena9, hterms9,
        htoks9, stage2NoEventWalkOfNat_add, stage2NoEventWalkCloserCarry,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcount9 : Stage2NoEventWalkCount (stage2NoEventWalkCloserCarry K 4)
      (k + 2 + 1) :=
    Stage2NoEventWalkCount.step (a := 1) (b := 1) e.count rfl rfl (by omega)
  let hentry9 : Stage2NoEventWalkAfterValueEntry calls mem
      (stage2NoEventWalkCloserCarry K 4) (k + 2 + 1) r9 :=
    stage2NoEventWalkAfterValueEntryOf (calls := calls) (mem := mem)
      (K := stage2NoEventWalkCloserCarry K 4) (k := k + 2 + 1) (s := r9)
      l9.inv' rfl sp3.toNat sp3.isLt (bytesToNat bsP)
      (stage2NoEventWalkBytesToNat_lt hbsLen) hcount9 "if.then350" rfl hsel9
      hbase9 e.bPos htrace9
  refine ⟨⟨r9, hentry9, hseg7.trans ⟨hrun, l9.inv'⟩, ?_, ?_⟩⟩
  · show r9.mem = s.mem
    have h1 : r9.mem = r8.mem := rfl
    rw [h1, hr8mem]
  · show sp3.toNat ≠ 0
    exact hdec

/-! ### The frame-zero close at `k + 3 = K.nep`

The parent's `}` at `k + 2` under a zero frame word: the committed
`stage2NoEventWalkFrameZeroBraceDeepEntry`'s nine blocks, with the endpoint
entry, its depth and its frame as data.  The entry, the `}` and the pop are the
caller's staging. -/

/-- **The frame-zero close as data**: nine blocks from the pair's `after_value`
entry at `k + 2` (its frame word zero, its next byte `}`) to the `after_value`
entry at `k + 3`, at the close-brace carry.  The endpoint's depth is
`%sp.4 - 1` and its frame the popped tag.

The route is the committed arm's; only the source's shape is assembled here. -/
theorem stage2NoEventWalkFrameZeroCloseArm {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (e : Stage2NoEventWalkAfterValueEntry calls mem K (k + 2) s)
    (hframeZero : e.frame = 0) (hspTwo : 2 ≤ e.sp)
    (hknep : K.nep = k + 3) (hk63 : k + 3 < 2 ^ 63)
    {lane2 : Nat} {byte2 : UInt8}
    (hk2 : K.ent[k + 2]? = some lane2) (hbs2 : K.bs[lane2]? = some byte2)
    (hbyte : byte2.toNat = 125)
    {a : Nat} {bs : List UInt8}
    (hpop : readBytes s.mem a 1 = some bs)
    (hpopAddr : a = closeReadAddr K.stk
      (BitVec.ofNat 32 e.sp + BitVec.ofNat 32 4294967294).toNat)
    (hbsLen : bs.length = 1) :
    ∃ (s' : State) (e' : Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 3) s'),
      Stage2NoEventWalkSegment calls mem K s
        (stage2NoEventWalkCloseBraceCarry K) s' 9 ∧
      e'.frame = bytesToNat bs ∧ e'.sp = e.sp - 1 := by
  have hframeLt : e.frame < 2 ^ 8 := e.frameLt
  let hsrc : Stage2NoEventWalkFrameZeroSrc calls mem K (k + 2) s :=
    { inv := e.inv, pc := e.pc, frame := e.frame, frameLt := hframeLt,
      frameZero := hframeZero, sp := e.sp, spLt := e.spLt, spNe := by omega,
      kAddr := by omega, klt := by omega, count := e.count, phiRun := e.phiRun,
      baseLookups := e.baseLookups, bPos := e.bPos, trace := e.trace }
  exact stage2NoEventWalkFrameZeroBraceDeepEntry hsrc hspTwo hk2 hbs2 hbyte
    hpop hpopAddr hbsLen

/-! ### The prices

The row's cost is `j + 3 ≤ Φ K k + F` at the head.  At `k + 3 = K.nep` the
head's potential carries three entries' allowance (`96`), which covers any
pair route up to sixteen blocks, any arm up to nine and the terminal's three.
No arm can be priced *from* `Φ K (k + 2)`: past the last entry `getD` defaults
to zero, so `Φ` jumps up at `K.nep` instead of falling. -/

/-- **The head's three entries' allowance**: `Φ K k ≥ 96` whenever `k + 3` is
inside the stream. -/
theorem stage2NoEventWalkPotential_three {K : Stage2NoEventWalkCarry} {k : Nat}
    (hk : k + 3 ≤ K.nep) : 96 ≤ stage2NoEventWalkPotential K k := by
  unfold stage2NoEventWalkPotential
  have hge : 3 ≤ K.nep - k := by omega
  have hmul : 32 * 3 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
  omega

/-- **The potential at the stream's end**: the entry's lane term is `getD`'s
default, so only the document's length remains. -/
theorem stage2NoEventWalkPotential_atNep {K : Stage2NoEventWalkCarry}
    (hent : K.ent.length = K.nep) :
    stage2NoEventWalkPotential K K.nep = 8 * K.n := by
  unfold stage2NoEventWalkPotential
  have hnone : K.ent[K.nep]? = none := by
    cases h : K.ent[K.nep]? with
    | none => rfl
    | some q =>
        have hlt : K.nep < K.ent.length := (List.getElem?_eq_some_iff.mp h).1
        omega
  have hd : K.ent.getD K.nep 0 = 0 := by
    rw [List.getD_eq_getElem?_getD, hnone]; rfl
  rw [hd]
  omega

/-- **The last step's potential does not fall.**  With the entry at `k`'s lane
`lane`, `Φ K k = 32 + 8 · (K.n - lane)` and `Φ K K.nep = 8 · K.n`, so a price
`p` from the endpoint needs `p + 8 · lane ≤ 32` — false for any lane above four.
This is why the row's cost is taken from the head's own three entries. -/
theorem Stage2NoEventPotentialLastJump {K : Stage2NoEventWalkCarry} {k lane : Nat}
    (hget : K.ent[k]? = some lane) (hk : k + 1 = K.nep) :
    stage2NoEventWalkPotential K k = 32 + 8 * (K.n - lane) := by
  unfold stage2NoEventWalkPotential
  have hgetD : K.ent.getD k 0 = lane := by
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  rw [hgetD, show K.nep - k = 1 from by omega]

/-- **The three arms' block counts are one entry's allowance**: the element
route's seven, the closers' nine, and the terminal's three are each `≤ 32`. -/
theorem stage2NoEventWalkContinueArmBlocks :
    (7 : Nat) ≤ 32 ∧ (9 : Nat) ≤ 32 ∧ (3 : Nat) ≤ 32 := by decide

/-! ### The rows at `k + 3 = K.nep`, live depth

Both rows take the class lane's pair route to the `after_value` entry at
`k + 2`, the parent's byte's arm, and the arm's terminal.  The pair's route is
the caller's segment (eleven blocks for `[]`, thirteen for `{}`), its endpoint
the caller's entry; the report, the route's frame and the refusal's witnesses
are the deployment boundary's, as the committed trailing rows take them. -/

/-- **The parent-closer `]` row at `k + 3 = K.nep`**, at a nested depth
(`2 ≤ sp`): the pair route, the parent's nine-block `]` arm, and the refusal at
the `after_value` entry it reaches (its stream spent at `k + 3 = K.nep`, its
depth `sp - 1 ≥ 1`).

Premises: `hleg`/`e` are the class lane's pair route and its endpoint; `hk3` is
the trailing index; `hframeNe`/`hspTwo`/`hsep` are the shape's own words and
byte; `hpop`/`hpopAddr`/`hbsLen` are the caller's stack staging;
`hreport`/`hrouteFrame` are the boundary's reference run and the push's frame;
`hdata` is the refusal's carried `obs`/`toks` and parser verdict. -/
noncomputable def stage2NoEventWalkBracketContinueDeepRow {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hleg : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s
      (stage2NoEventWalkPairCarry K) sE 11)
    (e : Stage2NoEventWalkAfterValueEntry (stage2NoEventCalls gap) mem
      (stage2NoEventWalkPairCarry K) (k + 2) sE)
    (hk3 : k + 3 = K.nep) (hk63 : k + 3 < 2 ^ 63)
    (hframeNe : e.frame ≠ 0) (hspTwo : 2 ≤ e.sp)
    (hsep : Stage2NoEventWalkParentSep (stage2NoEventWalkPairCarry K) k 93)
    {a : Nat} {bsP : List UInt8}
    (hpop : readBytes sE.mem a 1 = some bsP)
    (hpopAddr : a = closeReadAddr (stage2NoEventWalkPairCarry K).stk
      ((BitVec.ofNat 32 e.sp + BitVec.ofNat 32 4294967295) +
        BitVec.ofNat 32 4294967295).toNat)
    (hbsLen : bsP.length = 1)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)))
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  obtain ⟨s', e', hsegA, hmemA, hspNeA⟩ :=
    stage2NoEventWalkParentCloserDeepPoint (K := stage2NoEventWalkPairCarry K)
      e hframeNe hspTwo hsep (by show K.nep = k + 3; omega) hk63 hpop hpopAddr hbsLen
  have hsegAll : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4) s' (11 + 9) :=
    hleg.trans hsegA
  have hreport' : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem s'.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmemA]; exact hreport
  have hrouteFrame' : UnchangedOutside s.mem s'.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) := by
    rw [hmemA]; exact hrouteFrame
  have hpot : 96 ≤ stage2NoEventWalkPotential K k :=
    stage2NoEventWalkPotential_three (by omega)
  exact stage2NoEventWalkAfterValueRefuseRowOfEntry (gap := gap) (F := F)
    (k₀ := k) (k := k + 3) (j := 11 + 9)
    (K' := stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4)
    h htrace e' hsegAll.run e'.baseLookups (by omega) hspNeA (by omega) (by omega)
    hreport' hrouteFrame' hdata

/-- **The element `,` row at `k + 3 = K.nep`**, at a nested depth: the pair
route, the seven-block element route (its backedge guard zero because the entry
at `k + 3` does not exist), and `if.then`'s trailing refusal.

Premises: the pair route and its endpoint are the class lane's; `hk3` is the
trailing index; `hframeNe`/`hspNe`/`hcomma` are the shape's words and byte;
`hreport`/`hrouteFrame`/`hdata` are the boundary's. -/
noncomputable def stage2NoEventWalkBracketContinueElementRow {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hleg : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s
      (stage2NoEventWalkPairCarry K) sE 11)
    (e : Stage2NoEventWalkAfterValueEntry (stage2NoEventCalls gap) mem
      (stage2NoEventWalkPairCarry K) (k + 2) sE)
    (hk3 : k + 3 = K.nep) (hk63 : k + 3 < 2 ^ 63)
    (hframeNe : e.frame ≠ 0) (hspNe : e.sp ≠ 0)
    (hcomma : ∀ lane, (stage2NoEventWalkPairCarry K).ent[k + 2]? = some lane →
      (stage2NoEventWalkPairCarry K).bs.getD lane 0 = 44)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)))
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  obtain ⟨s', hsegA, hpc, hpre, hcmp, hmemA, hbaseA⟩ :=
    stage2NoEventWalkElementSpentArm (K := stage2NoEventWalkPairCarry K)
      e hframeNe hspNe hcomma (by show K.nep = k + 3; omega) hk63
  have hsegAll : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s
      (stage2NoEventWalkPairCarry K) s' (11 + 7) :=
    hleg.trans hsegA
  have hbase : Stage2NoEventWalkBaseLookups K s' := hbaseA
  have hpar : Stage2NoEventWalkParams K s' :=
    stage2NoEventWalkBaseLookups_params hbase
  have hloc : Stage2NoEventWalkLocals K s' :=
    stage2NoEventWalkBaseLookups_locals hbase h.inv.xjNext0
  have hw : lookupName s'.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hbase "%n" _ (by simp [stage2NoEventWalkBaseValues,
      stage2NoEventWalkParamEntries])
  have hle : (BitVec.ofNat 64 K.n).toNat ≤ K.n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  have hreport' : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem s'.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmemA]; exact hreport
  have hrouteFrame' : UnchangedOutside s.mem s'.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) := by
    rw [hmemA]; exact hrouteFrame
  have hpot : 96 ≤ stage2NoEventWalkPotential K k :=
    stage2NoEventWalkPotential_three (by omega)
  exact stage2NoEventZeroBlock_row (gap := gap) (F := F) (k := k)
    (sE := s') (blk := "if.then") (b := flushBlock) (w := "%n")
    (x := BitVec.ofNat 64 K.n) h hsegAll.run hpc flushBlock_find
    stage2NoEventFlushBlock_instrs rfl (by decide) hpar hloc hw hle
    (by omega) hreport' htrace hrouteFrame' hdata

/-! ### Axiom footprints -/

#print axioms outerBackedgeSpent_tail_denote
#print axioms outerBackedge_spent_leaf_denote
#print axioms stage2NoEventWalkElementSpentArm
#print axioms stage2NoEventWalkParentCloserDeepPoint
#print axioms stage2NoEventWalkFrameZeroCloseArm
#print axioms stage2NoEventWalkPotential_three
#print axioms stage2NoEventWalkPotential_atNep
#print axioms Stage2NoEventPotentialLastJump
#print axioms stage2NoEventWalkContinueArmBlocks
#print axioms stage2NoEventWalkBracketContinueDeepRow
#print axioms stage2NoEventWalkBracketContinueElementRow

end LeanLLVM.Refinement
