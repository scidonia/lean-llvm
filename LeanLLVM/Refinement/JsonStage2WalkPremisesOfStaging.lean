/-
# The walk's premises, from the staging

`WalkPremises` (`JsonStage2WalkAssembly`) had no producer: its two conjuncts — the empty
stream's flush and the loop's step — were stated and never applied, so
`stage2WalkCompletes_of_premises` and `stage2WalkObligation_of_premises` and the
`Stage2WalkObligation` they conclude were unapplied too.  This module builds the premise
from the record and the adapter's staging: the geometry and the staging are the two
constructions (`walkGeom_at_pre`, `walkStage_at_pre`), the seed's prefix and the
invariant at the loop head are theorems at them (`walkSeedPrefix_entry_geometry`,
`walkSeedInvariant_geometry`), and the two remaining conjuncts — the flush and the loop's
step — are composed here from the steps the layer already states.

## What is composed, and what is supplied

* **The flush**: `walkFlushSteps12`'s two steps, the refusal copy
  (`walkIfThenBlock_denote_named` at the state those two leave) and the return
  (`walkReturn_at`), composed by `WalkFlushAt.ofRun`.  Every read the copy takes is a
  word the staging fixes: the log's arena cursor and its event cursor
  (`walkEntryMemAt_alen`, `walkEntryMemAt_len` — `walkEntryMem_alen`'s and
  `walkEntryMem_len`'s twins at the adapter's own fold), and the refusal offset the
  flush block itself stores.  So the arm needs no hypothesis beside the staging.
* **The seed's prefix and the invariant at the loop head** are
  `walkSeedPrefix_entry_geometry` and `walkSeedInvariant_geometry`, applied at the
  constructed pair.  `WalkPremises` states both at the record's numbers while those two
  lemmas read `WalkStage`'s fields, so the staging is built by
  `walkStage_at_pre_fields` — `walkStage_at_pre`'s construction with the fields named.
* **The loop's step** is `walkLoopStep_of_staging`: `walkLoopStep_of_dispatch_exit` at a
  `WalkDispatch` and a `WalkExit`.  The exit is `walkExit_at_stage2Calls`, and the
  dispatch's continuing case is `walkRevolution_seg`'s composition restated with the
  merge's predecessor named (`walkRevolution_at`), because `WalkDispatch` states the
  predecessor and a segment's endpoint does not.

Four groups are premises, one per obstruction, and each is a bundle rather than a field
per fact:

| premise | what it is | why it is not derived |
|---|---|---|
| `WalkContinueFacts` | `HcontFacts` at every head state with an entry left | `walkRevolution_seg`'s own bundle, unweakened |
| `WalkMergeCells` | the merge's two register cells (`%inc.i`, `%nep`) and the header's index at the merge | `WalkSegment` records a run and an invariant, not the blocks it passed, so no lemma carries a register from the head to the merge; none of the three is a `WalkInv` clause |
| `WalkHeadPtrs` | `%z` and `%s` at the head | `WalkPtrs` names the six the dispatch reads and `walkStaticRegs` the twenty-four static addresses, and neither names these two; `WalkExit`'s own docstring records the same gap |
| `WalkLoopEnd` | `HlastFacts` and the exit's tail `ExitTail` at every last-entry head state | `walkExit_at_stage2Calls`' two arguments, at the states they are consumed |

`WalkInv.regs` does not close the pointer group either: the twenty-four names are `%s`'s
*fields* (`%nsp`, `%xp1`, `%n2.i`, …), the log's six addresses, the token's three, the
cursor's five and the four allocas; `%z` and `%s` themselves are not among them.

The bundle that produces the dispatch reads the pointer group at the same head states
the loop step does, which is why the two are supplied together
(`walkLoopStep_of_staging`).
-/

import LeanLLVM.Refinement.JsonStage2WalkExitProducer
import LeanLLVM.Refinement.JsonStage2WalkRevolution
import LeanLLVM.Refinement.JsonStage2WalkSeedAtEntry

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing entry's dispatch, with the merge's predecessor named -/

/-- **One continuing entry's dispatch to the merge**, at the terms `WalkDispatch` reads
them: the segment, the target block, the carry's index, the target's predecessor and
the price.  `walkRevolution_seg` states the segment and the price and leaves the
endpoint existential, which is all a completion needs; `WalkDispatch` also reads the
merge's `phi` selection, and that needs the predecessor the endpoint was entered from,
so the endpoint is named here.

The composition is `walkRevolution_seg`'s piece for piece — the head's counted `18`,
the scan's visits, the latch's exit and the merge's one step — and its price,
`18 + n + 2` against `32 + 8·ΔA`, is that lemma's arithmetic. -/
theorem walkRevolution_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (f : HcontFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      WalkInv G Cd sd ∧
      sd.pre = some "if.end473.i" ∧
      p + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) +
        stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  obtain ⟨s₀, hs₀, hsegP⟩ :=
    hlastPrefixSeg (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hge f.hpre5 f.hav5 f.hidx5 f.htok5 f.hgap5 f.hugt f.hpre6
      f.hin6 f.hv6 f.hend6 f.h8end f.hbit6 f.h8c f.hc110 f.hc116 f.hceq116 f.r₁ f.r₂
      f.r₃ f.ev f.hTail f.hpreS f.hincS f.hopS f.h3S f.hpos f.hreadS f.hbsS f.hloc105
      f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  have hsegP' : WalkSegment (stage2Calls stage2SubCalls) G C s (ScanLatchC C f.ev)
      (contLatchF f) ((((6 + 1) + 5) + 3) + 3) := by
    rw [hs₀] at hsegP
    exact hsegP
  have hcounter : lookupName (contLatchF f).env "%q.0.i246" =
      some (.int 64 (BitVec.ofNat 64 f.ei)) :=
    latch_counter (contEntryF f) (BitVec.ofNat 64 f.ei) f.a f.q f.x47
  have hbound : lookupName (contLatchF f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.cd)) := f.hcwL
  have hcdLt : f.cd < G.n := lt_of_le_of_lt f.hspan (entryPos_lt G hk)
  have hmax : G.n ≤ 2 ^ 32 := by
    have := G.maxDoc
    simpa only [stage2MaxDocument] using this
  have hc64 : f.cd < 2 ^ 64 := by omega
  have hc63 : f.cd ≤ 2 ^ 63 := by omega
  have heicd := f.heicd
  have hcd1 : 1 ≤ f.cd := by omega
  obtain ⟨Cm, sm, n, hsegR, hInvR, hbR, hiR, hcR, hnR⟩ :=
    contScanRounds G C s f hsegP'.inv' rfl hcounter hbound hc63 f.heicd
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hinner : f.cd - (f.cd - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR hc64 (by omega)
  have hie : (f.cd - 1) + 1 = f.cd := by omega
  obtain ⟨s₁, hseg₁, -, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie hc64 (by intro e _ _ _; simp [WalkLocal])
  obtain ⟨tok, htok⟩ := f.htok Cm sm hInvR hbR
  have htok₁ : lookupName s₁.env "%t352.i" = some (.ptr tok) := by
    rw [hs₁]
    exact scanExit_tok sm (f.cd - 1) f.cd htok
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := ScanCMerge Cm) (s := s₁)
      hInv₁ rfl htok₁
  have hpc₁ : s₁.pc = "if.end473.i" := by
    rw [hInv₁.pc_eq]
  have hpre₂ : s₂.pre = some "if.end473.i" := by
    rw [hs₂]
    show some s₁.pc = some "if.end473.i"
    rw [hpc₁]
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G C s
      { ScanCMerge Cm with block := "cleanup478.i" } s₂ (((18 + n) + 1) + 1) :=
    ((hsegP'.trans hsegR).trans hseg₁).trans (WalkSegment.of_link hl₂)
  refine ⟨{ ScanCMerge Cm with block := "cleanup478.i" }, s₂, ((18 + n) + 1) + 1,
    hseg, rfl, hseg.inv', hpre₂, ?_⟩
  have hd : f.cd - 1 - f.ei ≤ entryPos G (C.k + 1) - entryPos G C.k := by
    have h1 : f.cd - 1 ≤ entryPos G (C.k + 1) - 1 := Nat.sub_le_sub_right f.hspan 1
    have h2 : f.cd - 1 - f.ei ≤ (entryPos G (C.k + 1) - 1) - f.ei :=
      Nat.sub_le_sub_right h1 f.ei
    have h3 : (entryPos G (C.k + 1) - 1) - f.ei ≤
        (entryPos G (C.k + 1) - 1) - entryPos G C.k :=
      Nat.sub_le_sub_left f.hstart (entryPos G (C.k + 1) - 1)
    have h4 : (entryPos G (C.k + 1) - 1) - entryPos G C.k ≤
        entryPos G (C.k + 1) - entryPos G C.k :=
      Nat.sub_le_sub_right (Nat.sub_le (entryPos G (C.k + 1)) 1) (entryPos G C.k)
    exact le_trans h2 (le_trans h3 h4)
  have hn2 : n ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) :=
    le_trans hnR (Nat.mul_le_mul_left 8 hd)
  have hΔ : C.k + 1 - C.k = 1 := by omega
  simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one]
  have hl : 18 + n + 1 + 1 + 2 = n + 22 := by omega
  rw [hl]
  have h8 : n + 22 ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) + 22 :=
    Nat.add_le_add_right hn2 22
  have h22 : 8 * (entryPos G (C.k + 1) - entryPos G C.k) + 22 ≤
      32 + 8 * (entryPos G (C.k + 1) - entryPos G C.k) := by
    have hstep := Nat.add_le_add_left (by decide : (22 : Nat) ≤ 32)
      (8 * (entryPos G (C.k + 1) - entryPos G C.k))
    simpa only [Nat.add_comm] using hstep
  exact le_trans h8 h22

/-! ### The continuing entry's bundle, and the merge's cells -/

/-- **The continuing entry's facts at every head state with an entry left.**
`walkRevolution_seg`'s own bundle (`HcontFacts`), as a `∀`-producer: the statement a
dispatch needs is stated per head state, and this is the function that hands it one. -/
abbrev WalkContinueFacts {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontFacts G C s

/-- **The header's cells at the merge.**  `cleanup478.i`'s two `phi`s select the
dispatch's own registers — the depth `%sp.i.0248` and the index `%inc.i` — and the
carry's index is `%k.0.i249`, which only the header binds.  None of the three is a
`WalkInv` clause, and `WalkSegment` records a run and an invariant rather than the
blocks it passed, so no lemma carries a register from the head to the merge: this is
that group, stated where the dispatch reads it — at the endpoint of a segment from a
head state with an entry left.

The three facts are the model's: the scan's rounds and the latch's exit bind their own
cells, the merge binds `%k.2.i` and `%sp.i.1` rather than `%sp.i.0248`, and `%nep` is
an argument the walk never writes.  What is missing is the lemma, not the fact.

**Three conjuncts, and why none of them is a `WalkInv` field.**  Two are derivable from
invariant clauses that do not exist yet: `%inc.i = ofNat 64 (C.k + 1)` follows from the
header's one binding of `%inc.i` (`%k.0.i249 + 1`), so it holds wherever `blockIndex`
holds, and `%nep = ofNat 64 G.nep` from `%nep`'s being a parameter no block rebinds; at
`cleanup478.i` the merge binds only `%sp.i.1`, `%k.2.i` and `%cmp.i`, so a state-level
clause would read exactly these two cells.

The third — `Cd.k = C.k` — is *not* a state-level fact.  `WalkInv G C s` is indexed by
one state and one carry, so no field of it can relate two carries, and the equation is
lost inside `HcontFacts.hround`, whose target is existential (`∃ C'' s'', …`): the carry
`walkRevolution_at` reaches is that existential's, so `Cd.k` is opaque with it.

Adding the two clauses is a vocabulary change, and a scoping pass measured it: 39
`WalkInv` construction sites in 10 modules, `whileBody_step` (the only block that rebinds
`%inc.i`) and two new disequalities in `WalkPtrs.bind`/`WalkRegs.bind`.  It would retire
two fields of this premise and not the premise: the third conjunct survives it, because
it is a relation between carries rather than a fact about one.  So the three are
supplied together, and this is the reason. -/
abbrev WalkMergeCells {m0 : Mem} (G : WalkGeom m0) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep →
    ∀ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p → Cd.block = "cleanup478.i" →
      Cd.k = C.k ∧
      lookupName sd.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))

/-- The merge's `phi` for the depth, read off the block's incoming list. -/
theorem cleanupSpIncoming_at :
    phiIncoming "if.end473.i" cleanupSpIncoming = some (Operand.reg "%sp.i.0248") := by
  decide

/-- The merge's `phi` for the index, read off the block's incoming list. -/
theorem cleanupKIncoming_at :
    phiIncoming "if.end473.i" cleanupKIncoming = some (Operand.reg "%inc.i") := by
  decide

/-- **`WalkDispatch`, from the continuing bundle and the merge's cells.**  The
revolution's composition supplies the segment, the merge's block and the price; the
merge's own state supplies the depth `%sp.i.0248` (`WalkInv.depth_reg`) and the depth's
two bounds (`depth_cap`, `sp_le_wlen`); and `WalkMergeCells` supplies the carry's index
and the two cells the invariant does not bind.  The index the merge selects is
`C.k + 1`, the header's own increment, which the price's `Δk = 1` is stated at. -/
theorem walkDispatch_of_continue {m0 : Mem} {G : WalkGeom m0}
    (hcont : WalkContinueFacts G) (hmerge : WalkMergeCells G) :
    WalkDispatch (stage2Calls stage2SubCalls) G := by
  intro C s hInv hhead hk
  obtain ⟨Cd, sd, p, hseg, hblock, hInvD, hpre, hprice⟩ :=
    walkRevolution_at G C s hInv hhead hk (hcont C s hInv hhead hk)
  obtain ⟨hkC, hinc, hnep⟩ := hmerge C s hInv hhead hk Cd sd p hseg hblock
  have hdepth : evalOperand sd (Operand.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hInvD.depth_reg
  have hincv : evalOperand sd (Operand.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := hinc
  have hnep64 : G.nep < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
  refine ⟨Cd, sd, p, Cd.sp, C.k + 1, "if.end473.i", Operand.reg "%sp.i.0248",
    Operand.reg "%inc.i", BitVec.ofNat 64 G.nep, hseg, hblock, hkC, hpre,
    cleanupSpIncoming_at, hdepth, cleanupKIncoming_at, hincv, hnep, ?_, hk, ?_,
    hInvD.depth_cap, hInvD.sp_le_wlen, ?_⟩
  · rw [hnepv]; exact hk
  · omega
  · simpa only [Nat.add_sub_cancel] using hprice

/-! ### The exit, the pointer registers and the loop's step -/

/-- **The last entry's facts and the exit's tail**, at every head state the merge's
test sends to the exit.  This is `walkExit_at_stage2Calls`' two arguments, stated as
one premise: the bundle `HlastFacts` at the head, and the tail from the merge state the
bundle names. -/
structure WalkLoopEnd {m0 : Mem} (G : WalkGeom m0) (v : Value) : Type where
  /-- The last entry's facts, at every head state the merge's test sends to the exit. -/
  facts : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 = G.nep → HlastFacts G C s
  /-- The tail, from the merge state the bundle names. -/
  tail : ∀ (C : WalkCarry G) (s : State) (f : HlastFacts G C s),
    ExitTail (stage2Calls stage2SubCalls) (hlastMergeF f) v

/-- **The exit from the last entry's bundle.**  `walkExit_at_stage2Calls`' statement is
`WalkExit` at the record's selection, and its two arguments are `WalkLoopEnd`'s two
fields. -/
theorem walkExit_of_loopEnd {m0 : Mem} {G : WalkGeom m0} {v : Value}
    (h : WalkLoopEnd G v) : WalkExit (stage2Calls stage2SubCalls) G v :=
  walkExit_at_stage2Calls G h.facts h.tail

/-- **The two pointer registers the terminal block reads, at the head.**  `%z` and
`%s` are the log's and the staging record's addresses; the entry block binds them and
no block of the walk rebinds them, but neither is a `WalkInv` clause — `WalkPtrs` names
the six the dispatch reads and `walkStaticRegs` the twenty-four addresses, and `%z` and
`%s` are not among either — so the exit's statement names them and this is that group.

The facts are the entry environment's (`walkEntryState_env`); what is missing is a
carrier, not the fact: a `WalkSegment` records a run and an invariant, not the blocks
it passed, so no lemma carries a register from the entry to the head.

**A `WalkInv` carrier for them does not exist, and `regs` is not one.**  `WalkPtrs`
holds the six registers the dispatch reads, and `walkStaticRegs`' twenty-four names are
`%s`'s fields (`%nsp`, `%xp1`, `%n2.i`, …), the log's six addresses, the token's three,
the cursor's five and the four allocas.  `%z` and `%s` themselves appear in neither
list, so the pair is the input's, supplied at the same place the head's byte and its
class bits are. -/
abbrev WalkHeadPtrs {m0 : Mem} (G : WalkGeom m0) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    lookupName s.env "%z" = some (.ptr C.stage.z) ∧
    lookupName s.env "%s" = some (.ptr C.stage.s)

/-- **The loop's step, from the three bundles.**  `walkLoopStep_of_dispatch_exit`
asks for a dispatch, an exit and the two pointer registers; the dispatch is
`walkDispatch_of_continue`, the exit is `walkExit_of_loopEnd`, and the pair is
`WalkHeadPtrs` read at the head state the step is taken from. -/
theorem walkLoopStep_of_staging {m0 : Mem} {G : WalkGeom m0} {v : Value}
    (hcont : WalkContinueFacts G) (hmerge : WalkMergeCells G)
    (hptr : WalkHeadPtrs G) (hend : WalkLoopEnd G v) :
    WalkLoopStep (stage2Calls stage2SubCalls) G v 27 :=
  walkLoopStep_of_dispatch_exit (walkDispatch_of_continue hcont hmerge)
    (walkExit_of_loopEnd hend)
    (fun C s hInv hhead => (hptr C s hInv hhead).1)
    (fun C s hInv hhead => (hptr C s hInv hhead).2)

/-! ### The empty entry stream's flush, from the staging -/

/-- A store leaves the block: `walkSetMem` changes the memory and nothing else. -/
theorem walkSetMem_pc (s : State) (m : Mem) : (walkSetMem s m).pc = s.pc := rfl

/-- Naming a state at an environment leaves the block. -/
theorem stateAt_pc (env : Env) (s : State) : (stateAt env s).pc = s.pc := rfl

/-- **The refusal copy's state is at its input's block.**  The lemma is stated at the
general shape — the state and its memory as variables — because that shape is free and
the instance is not: the copy's state is a three-deep nest of `writeBytes`, and a `rfl`
at a *named* state's `.pc` exceeds 200 000 heartbeats deterministically (a `whnf`
timeout), while the same fact with the memory a variable is instant.  At a term whose
head is a variable the projection needs one unfold of each layer; at a named one it
unfolds the three writes and their byte lists at every position. -/
theorem walkIfThenBlockState_pc (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) : (walkIfThenBlockState env nd nv err e A L E s).pc = s.pc := by
  simp only [walkIfThenBlockState, stateAt_pc, walkSetMem_pc]

/-- The bytes written at an address are read back at it, at any width that spells
their length. -/
theorem readBytes_writeBytes_len {m : Mem} {bs : List UInt8} {a n : Nat}
    (h : n = bs.length) : readBytes (writeBytes m a bs) a n = some bs := by
  subst h
  exact readBytes_writeBytes_same m bs

/-- **A read inside the log's sixty-four bytes passes the entry run's later writes.**
The adapter's memory is the second segment's and the third's and the fourth's; this is
`walkEntryMem_read_out` with the header's store absent, which is the only difference
between the two folds. -/
theorem walkEntryMemAt_read_out {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a len : Nat} (hz0 : S.z ≤ a) (hz1 : a + len ≤ S.z + 64) :
    readBytes (walkEntryMemAt G S) a len =
      readBytes
        (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
          G.evcap
          (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
            ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)) a len := by
  obtain ⟨hcz, hzn⟩ := walkStage_log_sep G S
  show readBytes
      (walkSeg4PostMem (G.next0 + 8) (G.next0 + 12)
        (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
          (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
            G.evcap
            (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
              ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)))) a len = _
  rw [readBytes_walkSeg4PostMem_out (root := G.next0 + 8) (xj := G.next0 + 12)
    (by left; omega) (by left; omega)]
  rw [readBytes_walkSeg3PostMem_out (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
    (eAddr := S.e) (cAddr := S.c) ?_]
  intro st hst
  obtain ⟨hlo, hhi⟩ := walkSeg3Stores_bounds G.b G.n G.ep G.nep S.e S.c st hst
  rcases hcz with h | h <;> omega

/-- **The log's arena cursor at the adapter's memory.**  `walkEntryMem_alen`'s twin:
the read passes the third and fourth segments because it lies inside the log, and the
second segment is where the initialisation wrote the staged cursor. -/
theorem walkEntryMemAt_alen {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMemAt G S) (S.z + 48) 8 = some (wordBytes 8 G.ndst0) := by
  have h := walkEntryMemAt_read_out G S (a := S.z + 48) (len := 8) (by omega) (by omega)
  rw [h]
  have h2 := walkSeg2PostMem_alen (m := m0) (sAddr := S.s) (b := G.b) (ep := G.ep)
    (zAddr := S.z) (nep := G.nep) (xp := G.xp) (nxp := G.nxp) (dst := G.dst)
    (v1 := G.ndst0) (dstcap := G.dstcap) (ev := G.ev) (v2 := G.nev0) (evcap := G.evcap)
    (n := BitVec.ofNat 64 G.n) (nb := (BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6)
  simpa only [woff_48] using h2

/-- **The log's event cursor at the adapter's memory.**  `walkEntryMem_len`'s twin. -/
theorem walkEntryMemAt_len {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMemAt G S) (S.z + 8) 8 = some (wordBytes 8 G.nev0) := by
  have h := walkEntryMemAt_read_out G S (a := S.z + 8) (len := 8) (by omega) (by omega)
  rw [h]
  have h2 := walkSeg2PostMem_len (m := m0) (sAddr := S.s) (b := G.b) (ep := G.ep)
    (zAddr := S.z) (nep := G.nep) (xp := G.xp) (nxp := G.nxp) (dst := G.dst)
    (v1 := G.ndst0) (dstcap := G.dstcap) (ev := G.ev) (v2 := G.nev0) (evcap := G.evcap)
    (n := BitVec.ofNat 64 G.n) (nb := (BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6)
  simpa only [woff_8] using h2

/-- **The empty entry stream's flush, at the staging.**  At `nep = 0` the entry block
takes its zero arm, the flush block runs and the refusal copy writes the record's
three slots; `walkReturn_at` then returns the arm's literal zero.  The four steps are
`walkFlushSteps12`'s two, `walkIfThenBlock_denote_named`'s copy and `walkReturn_at`'s
return, and `WalkFlushAt.ofRun` composes them inside the finalisation allowance.

Every read the copy takes is a word the staging fixes: the log's arena cursor and its
event length (`walkEntryMemAt_alen`, `walkEntryMemAt_len`), and the refusal offset the
flush block's own store writes.  The three disjointness premises are the staged objects' — the log beside
the error record, and the two cursor slots beside it — so the arm needs nothing the
record does not supply. -/
theorem walkFlushAt_of_staging {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a13 : List Value} {next d : Nat}
    (h13 : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : next = G.next0) (hzero : G.nep = 0) :
    ∃ v0 : Value,
      WalkFlushAt (stage2Calls stage2SubCalls) v0 m0 next a13 G.nep d
        S.c S.ctype S.cst S.tok S.s S.z S.e := by
  obtain ⟨s₁, s₂, h1, h2, hpc2, hxj, hrd, halen, hlen, hc, hctp, hcst, hnd, hnev, he,
    herr, hmem2, henv2⟩ := walkFlushSteps12 (mem := m0) (d := d) G S hzero
  -- the two slots the copy reads, at the record's own offsets
  have hz48 : S.z + woff 48 = S.z + 48 := by rw [woff_48]
  have hz8 : S.z + woff 8 = S.z + 8 := by rw [woff_8]
  -- widths: the three staged words the copy reads
  have hn64 : G.n < 2 ^ 64 := by
    have h2' := G.maxDoc
    simp only [stage2MaxDocument] at h2'
    omega
  have hndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  have hnev0 : G.nev0 < 2 ^ 64 := by
    have hroom := G.evRoom
    have hcap := G.evcapLt
    omega
  -- the staged objects' separation, at the extents the stores lie in
  have hEZ : S.e + 24 ≤ S.z ∨ S.z + 64 ≤ S.e := by
    have h := staged_pair (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
      (xp := G.xp) (nxp := G.nxp) (dst := G.dst) (ndst0 := G.ndst0) (ev := G.ev)
      (evcap := G.evcap) (ndst := G.ndst) (nev := G.nev) (err := G.err)
      (c := S.c) (ctype := S.ctype) (cst := S.cst) (tok := S.tok) (sv := S.s)
      (z := S.z) (e := S.e) S.separate
      (r := (S.z, stage2LogExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
      (by
        intro hh
        have h2' : stage2LogExtent = stage2ErrorExtent := congrArg Prod.snd hh
        exact absurd h2' (by decide))
    have h' : S.z + 64 ≤ S.e ∨ S.e + 24 ≤ S.z := h
    omega
  have hEd : G.ndst + 8 ≤ S.e + 8 ∨ S.e + 8 + 8 ≤ G.ndst := by
    have h := walkRegion_against_writes S (r := (G.ndst, 8)) (by simp [stage2Regions])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2StagedWrites])
    have h' : G.ndst + 8 ≤ S.e ∨ S.e + 24 ≤ G.ndst := h
    omega
  have hEn : G.nev + 8 ≤ S.e + 8 ∨ S.e + 8 + 8 ≤ G.nev := by
    have h := walkRegion_against_writes S (r := (G.nev, 8)) (by simp [stage2Regions])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2StagedWrites])
    have h' : G.nev + 8 ≤ S.e ∨ S.e + 24 ≤ G.nev := h
    omega
  have hZd : G.ndst + 8 ≤ S.z + woff 8 ∨ S.z + woff 8 + 8 ≤ G.ndst := by
    have h := walkRegion_against_writes S (r := (G.ndst, 8)) (by simp [stage2Regions])
      (q := (S.z, stage2LogExtent)) (by simp [stage2StagedWrites])
    have h' : G.ndst + 8 ≤ S.z ∨ S.z + 64 ≤ G.ndst := h
    omega
  -- the copy's three reads, at the memory the flush block leaves
  have hmem : s₂.mem = writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n) := hmem2
  -- the return's two other registers: the entry environment's, untouched on the arm
  have hz₂ : lookupName s₂.env "%z" = some (.ptr S.z) := by
    rw [henv2]
    simp [walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells,
      lookupName_cons_ne, walkEntryState_env]
  have hs₂ : lookupName s₂.env "%s" = some (.ptr S.s) := by
    rw [henv2]
    simp [walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells,
      lookupName_cons_ne, walkEntryState_env]
  have hA : readBytes s₂.mem (S.z + woff 48) 8 =
      some (natToBytes (BitVec.ofNat 64 G.ndst0).toNat 8) := by
    rw [hmem, hz48]
    have hout : S.z + 48 + 8 ≤ S.e + 8 ∨ S.e + 8 + (wordBytes 8 G.n).length ≤ S.z + 48 := by
      have hl : (wordBytes 8 G.n).length = 8 := by simp [wordBytes, natToBytes_length]
      omega
    rw [walkReadBytes_writeBytes_outside (m := walkEntryMemAt G S) (v := wordBytes 8 G.n)
      (start := S.e + 8) (addr := S.z + 48) (n := 8) hout]
    rw [walkEntryMemAt_alen G S]
    rw [show (BitVec.ofNat 64 G.ndst0).toNat = G.ndst0 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hndst0]]
    rfl
  have hL : readBytes s₂.mem (S.z + woff 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.nev0).toNat 8) := by
    rw [hmem, hz8]
    have hout : S.z + 8 + 8 ≤ S.e + 8 ∨ S.e + 8 + (wordBytes 8 G.n).length ≤ S.z + 8 := by
      have hl : (wordBytes 8 G.n).length = 8 := by simp [wordBytes, natToBytes_length]
      omega
    rw [walkReadBytes_writeBytes_outside (m := walkEntryMemAt G S) (v := wordBytes 8 G.n)
      (start := S.e + 8) (addr := S.z + 8) (n := 8) hout]
    rw [walkEntryMemAt_len G S]
    rw [show (BitVec.ofNat 64 G.nev0).toNat = G.nev0 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnev0]]
    rfl
  have hE : readBytes s₂.mem (S.e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.n).toNat 8) := by
    rw [hmem]
    rw [readBytes_writeBytes_len (bs := wordBytes 8 G.n) (n := 8)
      (by simp [wordBytes, natToBytes_length])]
    rw [show (BitVec.ofNat 64 G.n).toNat = G.n by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
    rfl
  -- the copy itself, in its named state
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs s₂ =
      some (walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
        (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂) := by
    have h := walkIfThenBlock_denote_named (sub := stage2SubCalls) (env := s₂.env) (s := s₂)
      hxj hrd hcst hctp hc halen hnd hlen hnev he herr hA hL hE hZd hEd hEn
    rwa [stateAt_self] at h
  have hpc₃ : (walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
      (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂).pc
      = s₂.pc := walkIfThenBlockState_pc _ _ _ _ _ _ _ _ _
  obtain ⟨s₃, h3, hpc₃', henv₃, hpre₃⟩ :=
    walkRefusalCopy_at (sub := stage2SubCalls) (s := s₂)
      (s₁ := walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
        (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂)
      hpc2 hden hpc₃
  -- the return, at the refusal arm's literal zero
  have hcells := walkRefusalCopyState_cells s₂.env G.ndst G.nev G.err S.e
    (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂
  have hpre₃' : s₃.pre = some "if.then" := by
    rw [hpre₃, hpc2]
  obtain ⟨s₄, h4⟩ := walkReturn_at (sub := stage2SubCalls) (s := s₃) hpc₃'
    (by rw [henv₃]; exact hcells.1.trans he) (by rw [henv₃]; exact hcells.2.1.trans hz₂)
    (by rw [henv₃]; exact hcells.2.2.trans hs₂) hpre₃' walkIfEnd_refusal_phi rfl
  exact ⟨.int 64 0, WalkFlushAt.ofRun (sub := stage2SubCalls) (v0 := .int 64 0)
    (nep := G.nep) (mem := m0) (next := next) hzero
    (by rw [h13, hnext]; exact h1) h2 h3 h4⟩

/-! ### The staging at the record's own numbers -/

/-- **The adapter's staging, at the record's numbers.**  `walkStage_at_pre` constructs
the `WalkStage` from the staged predicate's witnesses, so its fields *are* the record's
— `c`, `ctype`, `cst`, `tok`, `s`, `z`, `e` and `d`.  That is a fact about the
construction and not about an arbitrary staging, and it is what the flush and the seed
read: `WalkPremises` states both at the record's numbers, while the two lemmas that
produce them are stated at the staging's.

The construction is `walkStage_at_pre`'s, with the fields named; the geometry and the
disjointness are that lemma's own. -/
theorem walkStage_at_pre_fields {args : List Value} {m0 : Mem} {next : Nat}
    {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hpre : Γ_stage2.pre args m0 next)
    (hst : stage2StagedPre args m0 next d c ctype cst tok s z e nkSlot nxpSlot) :
    ∃ (G : WalkGeom m0) (S : WalkStage G), G.next0 = next ∧
      S.c = c ∧ S.ctype = ctype ∧ S.cst = cst ∧ S.tok = tok ∧ S.s = s ∧
      S.z = z ∧ S.e = e ∧ S.d = d ∧
      args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] := by
  obtain ⟨G, hnext, hargs⟩ := walkGeom_at_pre hpre
  obtain ⟨hpres, hd8, b', nw, ep', nepw, xp', nxpw, dst', dstcapw, ndst0', ev', evcapw,
    ndst', nev', err', hargs', hread', hdisj', hndst0w, hwm'⟩ := hst
  obtain ⟨-, -, -, -, -, -, -, -, hndstEq, -, -, -, -⟩ :=
    stage2Args_components hargs hargs'
  have hmod : G.ndst0 % 2 ^ 64 = ndst0' % 2 ^ 64 := by
    have hreadG : readBytes m0 ndst' 8 = some (wordBytes 8 G.ndst0) := by
      rw [← hndstEq]; exact G.ndstRead
    exact wordBytes8_mod_eq (Option.some.inj (hreadG.symm.trans hread'))
  have hGndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  have hrecon := stage2StagedRegions_reconcile hargs hargs' (WalkGeom.n_lt G)
    (WalkGeom.nep_lt G) G.nxpLt G.dstcapLt G.evcapLt hGndst0 hndst0w hmod
    c ctype cst tok s z e nkSlot nxpSlot
  have hdisjG : DisjointRegions
      ((stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
          G.ndst G.nev G.err c ctype cst tok s z e ++ [(d, 8)]) ++
        [(nkSlot, 8), (nxpSlot, 8)]) := by
    rw [← hrecon] at hdisj'
    simpa only [stage2StagedRegions, List.append_assoc] using hdisj'
  refine ⟨G, WalkStage.mk c ctype cst tok s z e nkSlot nxpSlot ?_ hpres d hd8 ?_ ?_,
    hnext, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hargs⟩
  · exact walkDisjoint_drop_member hdisjG
  · have hL : DisjointRegions
        (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
          G.ndst G.nev G.err c ctype cst tok s z e ++
          [(d, 8), (nkSlot, 8), (nxpSlot, 8)]) := by
      simpa only [List.append_assoc, List.singleton_append] using hdisjG
    unfold DisjointRegions at hL
    rw [List.pairwise_append] at hL
    obtain ⟨-, -, hcross⟩ := hL
    exact fun r hr => hcross r hr (d, 8) (by simp)
  · rw [hnext]; exact hwm'

/-! ### The premises, from the record and the staging -/

/-- **`WalkPremises` from the record's staging.**  The two branches are the record's
own: at `G.nep = 0` the entry block's zero arm runs the flush (`walkFlushAt_of_staging`,
which needs nothing the staging does not supply), and with entries left the seed's
prefix and the invariant at the loop head are the two theorems at the constructed pair
(`walkSeedPrefix_entry_geometry`, `walkSeedInvariant_geometry`) and the loop's step is
`walkLoopStep_of_staging` at the three bundles.

The stage is `walkStage_at_pre_fields`', so the flush and the seed are stated at the
record's numbers: those lemmas read `WalkStage`'s fields, `WalkPremises` names the
record's, and the fields' equalities are the construction's.

The three bundles are the premises, one group each: the continuing entry's facts, the
merge's cells, the head's two pointer registers and the last entry's facts with the
exit's tail. -/
theorem walkPremises_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkContinueFacts G)
    (hmerge : ∀ {m0 : Mem} (G : WalkGeom m0), WalkMergeCells G)
    (hptr : ∀ {m0 : Mem} (G : WalkGeom m0), WalkHeadPtrs G)
    (hend : ∀ {m0 : Mem} (G : WalkGeom m0), Σ' v : Value, WalkLoopEnd G v) :
    WalkPremises d c ctype cst tok s z e nkSlot nxpSlot := by
  intro a13 mem next hpre hst
  obtain ⟨G, S, hnext, hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd, hargs⟩ :=
    walkStage_at_pre_fields hpre hst
  refine ⟨mem, G, S, hnext, hargs, ?_⟩
  by_cases hzero : G.nep = 0
  · left
    obtain ⟨v0, hv⟩ := walkFlushAt_of_staging G S hargs hnext.symm hzero
    exact ⟨hzero, v0, by
      simpa only [hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd] using hv⟩
  · right
    have hpos : 0 < G.nep := Nat.pos_of_ne_zero hzero
    refine ⟨hpos, ?_, ?_, ?_⟩
    · -- the seed's three-step prefix to the loop head
      intro n
      have h := walkSeedPrefix_entry_geometry (d := d) G S hargs hnext.symm hpos n
      simpa only [hSc, hSct, hScs, hStok, hSs, hSz, hSe, hSd] using h
    · -- the invariant at the loop head
      refine walkSeedInvariant_geometry G S
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
        hpos ?_ ?_ ?_
      · rw [hargs, walkEntryState_env, hSct]
        simp [lookupName]
      · rw [hargs, walkEntryState_env, hScs]
        simp [lookupName]
      · exact hnext.symm
    · -- the loop's step, at the exit's own value
      obtain ⟨v, hendv⟩ := hend G
      exact ⟨v, walkLoopStep_of_staging (G := G) (hcont G) (hmerge G) (hptr G) hendv⟩

/-! ### The completion and the walk's obligation

`stage2WalkCompletes_of_premises` and `stage2WalkObligation_of_premises` were stated and
never applied; these are their applications at the premises above.  Nothing new is
proved: the two conditionals' own statements are read at `walkPremises_of_staging`.

The obligation's second argument is the record's post rule, which
`stage2WalkObligation_of_premises` names and this layer does not read: it is the run's
region claim at the outcome, and `stage2Post_of_run` is what produces it from a
`Stage2Run` and a completion.  It is a hypothesis here for the same reason it is one
there — the state's post is not the walk's statement.
-/

/-- **The completion, from the four premises.**  `stage2WalkCompletes_of_premises` at
`walkPremises_of_staging`: the body's run reaches an outcome inside the record's budget
whenever the record's pre and the adapter's staging hold. -/
theorem stage2WalkCompletes_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkContinueFacts G)
    (hmerge : ∀ {m0 : Mem} (G : WalkGeom m0), WalkMergeCells G)
    (hptr : ∀ {m0 : Mem} (G : WalkGeom m0), WalkHeadPtrs G)
    (hend : ∀ {m0 : Mem} (G : WalkGeom m0), Σ' v : Value, WalkLoopEnd G v) :
    Stage2WalkCompletes d c ctype cst tok s z e nkSlot nxpSlot stage2SubCalls :=
  stage2WalkCompletes_of_premises (walkPremises_of_staging hcont hmerge hptr hend)

/-- **The walk's obligation, from the four premises and the record's post.**  This is
the milestone the layer was built for: `Stage2WalkObligation` is `Satisfies` at
`Γ_stage2at`, and its completion half is `stage2WalkCompletes_of_staging`; its post
half is the record's own, named. -/
theorem stage2WalkObligation_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkContinueFacts G)
    (hmerge : ∀ {m0 : Mem} (G : WalkGeom m0), WalkMergeCells G)
    (hptr : ∀ {m0 : Mem} (G : WalkGeom m0), WalkHeadPtrs G)
    (hend : ∀ {m0 : Mem} (G : WalkGeom m0), Σ' v : Value, WalkLoopEnd G v)
    (hpost : ∀ args mem next,
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).pre args mem next →
      ∀ o, BehFromState (stage2Calls stage2SubCalls) stage2Body
          (EntryState stage2Body args mem next) o →
        (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post args mem next o) :
    Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot :=
  stage2WalkObligation_of_premises (walkPremises_of_staging hcont hmerge hptr hend) hpost

/-! ### The four premises, and what each one owes

The composition is complete; what remains is one premise per obstruction, and this is
the map.  None of the four is a gap in the composition — each is either a fact about
the input or a named missing preservation lemma.

| premise | status |
|---|---|
| `WalkContinueFacts` | **`HcontFacts`' own supply, in `HlastFacts`' discipline.**  Its producer is `hlastFacts_of_staging`'s twin — the same three sources (the invariant's clauses, the document's content, the staging's addresses) read at the same states — and the bundle's fields are the head's byte and its four class bits, the entry counts and the default arm's cells, the seam's cells and the scan's landing.  Two groups it cannot produce: the traversal's three hypotheses (`hround`, `hguard`, `hbyte`, supplied unweakened) and `htok`, which needs *the extra-token scan preserves a register it does not bind* — a statement a `WalkSegment` cannot carry, because the traversal returns its final state existentially. |
| `WalkMergeCells` | **structural, and no producer can exist in this vocabulary.**  `WalkSegment` records a run and an invariant, and neither names the blocks the run passed or the registers they bound; no lemma in the layer carries a register across a segment, so `%inc.i`, `%nep` and the header's index at the merge cannot be read off the segment that reaches it.  A producer needs a segment-level register-preservation statement, which the vocabulary does not have. |
| `WalkHeadPtrs` | **the input's, like the class bits.**  `%z` and `%s` are bound by the entry block (`walkEntryState_env`) and by nothing else; no `WalkInv` clause names them (`WalkPtrs` has the dispatch's six, `walkStaticRegs` the twenty-four addresses), so the pair is supplied at the point a caller knows the staging. |
| `WalkLoopEnd` | **supplied, with its first half's producer already in the tree.**  `facts` is `HlastFacts`, whose producer is `hlastFacts_of_staging` (which itself takes a bundle of supplied facts — the head's byte and class bits, the register cells and the calls' outcomes — so its own supply is the same discipline); `tail` is `ExitTail`, which `walkExit_at_stage2Calls` takes from the caller as the three calls' contracts composed at their staged argument lists. |

Of the four, `WalkMergeCells` is the one with no producer of any shape: the other three
are supplies a caller makes from the input, and this one is a statement the layer has
no vocabulary to state. -/

/-! ### Axiom footprints beyond the five -/

#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkCompletes_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkObligation_of_staging

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkRevolution_at
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_of_continue
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStep_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushAt_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkPremises_of_staging

end WalkScope
end LeanLLVM.Refinement
