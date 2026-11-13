/-
The stage-2 walk's assembly: the loop step composed out of its edges, and the
completion at the ABI's own arguments.

`JsonStage2WalkTraverse` reads the loop as an induction on the entry index and
leaves one premise, `WalkLoopStep`, whose left branch is a whole revolution of the
dispatch and whose right branch is the exit.  This module takes the revolution
apart:

* **the back edge's target state is exposed.**  `walkBack_step` states the merge's
  step, the invariant at the target and the run, but the target is existential, so
  the `%k.2.i`/`%sp.i.1` bindings the header's pass reads cannot be recovered from
  it.  `cleanup478Out` names the state, `walkBack_step_at` states the same four
  facts at it, and the bindings are then by definition rather than by hypothesis.
  The composition is what that obstruction was blocking: `walkBack_step_at` feeds
  `whileBody_step`'s hypotheses directly, so a revolution is the dispatch's
  segment, the merge's step and the header's pass, in that order;
* **the revolution is one segment**, priced by the dispatch's own segment and
  spent against the potential (`WalkDispatch.revolution`), and the loop step is
  then a case split on the entry index (`walkLoopStep_of_dispatch_exit`): while
  `k + 1 < nep` the dispatch runs and the merge's test is clear, and at `k + 1 = nep`
  the test fails and the exit's tail runs.  The split is not decoration — the
  merge's guard is `k2 < nep`, so a dispatch premise asserted at every head state
  would be false at the last one, and `WalkLoopStep`'s exit branch is available
  exactly where the revolution is not;
* **the two loop premises are named**, `WalkDispatch` (the dispatch's chain from
  the head to `cleanup478.i`, with the ten predecessors' `phi` facts at the merge,
  the index's strict advance and the potential's spending) and `WalkExit` (the
  false edge, the tail through `s2_walk.exit` and `if.end`'s return, inside the
  finalisation allowance);
* **the finalisation allowance is arithmetic** (`walkExitFits`): `F ≤ 27` at the
  seed's three steps is `3 + F + 2 ≤ stage2FinalisationAllowance`, by the record's
  own constant;
* **the geometry is a construction** (`walkGeom_at_pre`): `stage2Pre`'s thirteen
  witnesses and its clauses are `WalkGeom`'s fields and clauses, and the argument
  list is the geometry's own numbers, so the completion's budget at `a13` is the
  budget at the geometry;
* **the completion at the ABI's arguments** (`stage2WalkCompletes_of_premises`): at
  every staging the record admits, the seed's three-step prefix, the invariant at
  the loop head and the loop's step give `Stage2WalkCompletes` — the first conjunct
  of `Stage2WalkObligation` beside the post
  (`stage2WalkObligation_iff_completion`).

Premise 4 is now discharged: the geometry is `walkGeom_at_pre` and the stage
`walkStage_at_pre`, so `walkPremises_of_parts` states the seed's run, the invariant
and the loop's step at a pair the record *gives* rather than one a proof invents.

What the module does not do is inhabit `Stage2WalkObligation`: the loop step's two
premises are the census's dispatch chain and the exit's tail, and the post half is
untouched here.  Those three are stated, not assumed away, and
`stage2WalkCompletes_of_premises`/`stage2WalkObligation_of_premises` is the exact
shape of what a dispatch supplies.

The seed's residue is not a trace and is enumerated rather than assumed.  The three
block runs `walkSeedPrefix_runFuel` takes are `entry`'s fifty-seven instructions
(`walkEntry_denote`), `while.body.i.lr.ph`'s five `getelementptr`s
(`walkPreheader_denote`) and `while.body.i`'s first pass
(`whileBodyFirst_denote`), plus the entry test's bit and the header's two loads.
`walkEntry_denote`'s hypothesis list is what the residue is made of, and every item
in it is one of four kinds: the eighteen register bindings, which are
`EntryState`'s own argument list read at `stage2Body.params`; five region-separation
facts, which are `WalkStage.separate` at the two cursor slots; the two cursor-slot
reads, which are the geometry's `ndstRead`/`nevRead`; and the word facts —
`0 < G.b`, `G.b < 2^64`, `G.ep < 2^64`, and the counts `G.nxp`, `G.dstcap`,
`G.evcap`, `G.ndst0`, `G.nev0` inside their words.  Every one of them is the
precondition's: `Γ_stage2.pre` states the three counts (`nxp`, `dstcap`, `evcap`),
the two addresses (`0 < b`, `b < 2^64`, `ep < 2^64`), and `nep` follows from the
stream, which is what `Stage2Run`'s
`nxpLt`/`dstcapLt`/`evcapLt`/`nepLt`/`bPos`/`bLt`/`epLt` read at the *report*, and
`G.n` is below the document's `2 ^ 32` bound (`WalkGeom.n_lt`).  So the seed's
three runs are environment reads, not a trace — the record grants every fact they
ask — which is why the four premises reduce to the dispatch's chain and the exit's
tail.  The final state is `walkSeedFinalState`, whose cursor is the entry run's
`next + 28` (the four `alloca`s `stage2AllocaWrites` names); the state the three
blocks leave and the state the loop reads are one state, field for field.
-/
import LeanLLVM.Refinement.JsonStage2WalkSeedRun
import LeanLLVM.Refinement.JsonStage2WalkTraverse

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-! ### The merge's target state, named

`walkBack_step` builds its target inside the proof, so its conclusion's `e` is
existential and the two `phi` bindings the header's pass consumes are not
recoverable from it.  The block's own state is a definition: the two `phi`s the
incoming edge selects and the test, at the block the test branches to. -/

/-- **`cleanup478.i`'s target**: the merge's two `phi` selections and the test's
bit, entering `while.body.i` from `cleanup478.i`. -/
def cleanup478Out (s : State) (spv k2 : Nat) : State :=
  { ((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
      "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
      "%cmp.i" (.int 1 (1 : BitVec 1)) with
    pc := "while.body.i", pre := some "cleanup478.i" }

/-- The merge's target carries the index the back edge selected. -/
theorem cleanup478Out_k {s : State} {spv k2 : Nat} :
    lookupName (cleanup478Out s spv k2).env "%k.2.i" =
      some (.int 64 (BitVec.ofNat 64 k2)) := by
  simp only [cleanup478Out, State.bind]
  rw [lookupName_cons_ne (k := "%cmp.i") (n := "%k.2.i") (h := by decide)]
  exact lookupName_cons_self _ _ _

/-- The merge's target carries the depth the back edge selected. -/
theorem cleanup478Out_sp {s : State} {spv k2 : Nat} :
    lookupName (cleanup478Out s spv k2).env "%sp.i.1" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
  simp only [cleanup478Out, State.bind]
  rw [lookupName_cons_ne (k := "%cmp.i") (n := "%sp.i.1") (h := by decide)]
  rw [lookupName_cons_ne (k := "%k.2.i") (n := "%sp.i.1") (h := by decide)]
  exact lookupName_cons_self _ _ _

/-- The merge's target is entered from the merge. -/
theorem cleanup478Out_pre {s : State} {spv k2 : Nat} :
    (cleanup478Out s spv k2).pre = some "cleanup478.i" := rfl

/-- The merge's target is `while.body.i`. -/
theorem cleanup478Out_pc {s : State} {spv k2 : Nat} :
    (cleanup478Out s spv k2).pc = "while.body.i" := rfl

/-- **The back edge, at the state the next pass reads.**  `walkBack_step`'s four
facts at `cleanup478Out`, so the header's pass has its two `phi` values and its
predecessor without a hypothesis beside them. -/
theorem walkBack_step_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup478.i")
    {p : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) :
    step calls stage2Body s = .jump (cleanup478Out s spv k2) ∧
    WalkInv G { C with block := "while.body.i", inner := walkInnerCap G }
      (cleanup478Out s spv k2) ∧
    (∀ n, runFuel calls (1 + n) stage2Body s =
      runFuel calls n stage2Body (cleanup478Out s spv k2)) := by
  obtain ⟨e, hstep, hinv, hrun⟩ :=
    walkBack_step G C s hInv hblock hpre hsp hspv hk hkv hnep hguard
  have hpc : s.pc = "cleanup478.i" := by rw [hInv.pc_eq, hblock]
  have hden := cleanup478_denote calls s p hpre hsp hspv hk hkv hnep hguard
  have hterm : cleanup478Block.term =
      Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" := rfl
  have hfind : stage2Body.findBlock s.pc = some cleanup478Block := by
    rw [hpc, cleanup478_find]
  have hcanon : step calls stage2Body s = .jump (cleanup478Out s spv k2) := by
    simp only [step, hfind, hden, hterm]
    dsimp only [cleanup478Out, State.bind]
    simp only [execTerm, evalOperand, lookupName_cons_self, hpc]
    simp
  have heq : e = cleanup478Out s spv k2 :=
    Ctrl.jump.inj (hstep.symm.trans hcanon)
  subst heq
  exact ⟨hcanon, hinv, hrun⟩

/-! ### The loop's two premises

`WalkLoopStep`'s left branch is the revolution; its right branch the exit.  Stated
separately, they are the census's remaining two rows: the dispatch's trace through
the 157 links and the ten predecessors' `phi` facts at `cleanup478.i`, and the
false edge's tail to the return. -/

/-- **The dispatch's chain, and the merge it reaches.**  At the head, with an
unconsumed entry left *after* this iteration (`C.k + 1 < G.nep`, which is the
merge's own guard at `%inc.i = C.k + 1`), the dispatch runs to `cleanup478.i`
leaving the carry's index where the head put it, the merge's two `phi` operands of
the block that jumped there, an index `k2` strictly advanced and still short of
the stream, a depth inside the stacks, and a price inside the credit it consumes:
the dispatch's own count plus the merge's and the header's two steps, against
`32·Δk + 8·ΔA` — one entry allowance per entry consumed and one byte allowance per
document byte the entry spans.  The two steps are named in the premise because they
are steps the revolution takes and the credit is charged for them: one iteration's
own path is `stage2EntryAllowance` (`32`) and the merge and the header are the last
two blocks in it.  The byte term is what pays the scans: an entry's dispatch runs
inside the bytes between its position and the next entry's. -/
def WalkDispatch (calls : Calls) {m0 : Mem} (G : WalkGeom m0) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep →
    ∃ (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64),
      WalkSegment calls G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      Cd.k = C.k ∧
      sd.pre = some prev ∧
      phiIncoming prev cleanupSpIncoming = some spOp ∧
      evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)) ∧
      phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧
      k2 < nepv.toNat ∧
      k2 < G.nep ∧
      C.k < k2 ∧
      spv ≤ stage2StackExtent ∧
      spv ≤ Cd.wlen ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)

/-- **The exit**: at the head whose merge fails its test (`C.k + 1 = G.nep`, so
`%inc.i` is the entry count), `27` steps reach a state whose jump is followed by a
return — *beside* the potential the state still holds, because that state's own
dispatch is the last entry's.  The `27` is the finalisation allowance less the
seed's three steps and the two terminal ones (`walkExitFits`). -/
def WalkExit (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (v : Value) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 = G.nep →
    ∃ (q : Nat) (s1 s2 sret : State),
      q ≤ walkPotential G C + 27 ∧
      (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
      step calls stage2Body s1 = .jump s2 ∧
      step calls stage2Body s2 = .ret v sret

/-! ### What a dispatch proof still owes

Two things the census's links do not supply, and the dispatch therefore owes
itself.  A `WalkLink`'s target state is *existential* (`∃ s', WalkLink … s'`), so a
chain of them leaves the state at `cleanup478.i` unnamed and the merge's two `phi`
operand values — `%inc.i`, and the container arm's `%inc208.i` or `%sub.i` — cannot
be read off it; and a link's price is `walkMeasure`'s non-increase, not the credit
the potential charges, so the chain says nothing about the price premise.  A
dispatch proof is therefore a per-block run at the *values* the next block reads
(the shape `WalkLink.addImmBr` and the named-environment statements in
`JsonStage2WalkPure` already take), not a chain of the existing links.

**The price's path and the trace.**  The dispatch is a switch over the token, so a
proof covers every branch, and the run is written over the blocks reachable from the
head without passing the merge — `walkDispatchReach`, **156 blocks**, the four trap
blocks included (`walkTrap_noStep`).  The *price* is much smaller than that: over
the same graph with the five scans' repeated visits removed (the ten blocks
`walkScanBlocks` names), the longest path from `while.body.i` to the merge is
twenty-two steps:

  `while.body.i → NodeBlock21 → NodeBlock5 → NodeBlock → LeafBlock1 → sw.default.i
  → cond.true345.i → cond.end349.i → land.lhs.true357.i → NodeBlock41 → NodeBlock39
  → LeafBlock35 → if.end372.i → if.else387.i → NodeBlock62 → NodeBlock60 →
  LeafBlock56 → if.then403.i → if.then413.i → if.then425.i → if.then447.i →
  if.end473.i → cleanup478.i`

`walkDispatchPrice` is `some 22` and `walkDispatch_le_entryAllowance` is that count
against `stage2EntryAllowance`.  `WalkDispatch` is stated at the head
(`NodeBlock21`, one step into the path), so the dispatch's own count is at most
twenty-one and `p + 2` — the merge and the header's pass — is at most twenty-three,
inside the `22 + 2` the credit's rows use.  The price is a bound on one path; the
ten blocks `walkScanBlocks` names are charged per document byte instead
(`walkScanStepSets`, `walkScanStepWidth_le_byteAllowance`), which is how 156 blocks'
worth of trace fits twenty-one steps' worth of entry allowance.

**What naming costs.**  Each block's step must be computed at the concrete
environment the invariant fixes, so that `Ctrl.jump`'s injectivity names the
successor: `step calls stage2Body s = .jump sN` from a `simp` at the block's
`denoteCode` and terminator, then `WalkLink`'s existential target is `sN` by
`Ctrl.jump.inj` — the pattern `walkBack_step_at` uses at the merge.  Four of the
dispatch's twenty-one have a `_denote` at the block (`walkCondEnd349_denote`,
`walkIfThen413I_denote`, `walkIfThen425_denote`, `walkIfThen447I_denote`; the merge
has `cleanup478_denote`); the rest of the trace has a `WalkLink` at each block's own name except the five scan
latches (`forInc`, `scanLanding`), the four trap blocks, `if.end24.i` (`ifEnd24`),
`if.then425.i` (the pair `if_then425_i_emit`/`_refuse`) and the return's two blocks
(`if.end`, `if.then`, whose runs are `walkIfEnd_step` and `walkIfThen_step`); each
block's `denoteCode` is derived inside its link's proof, so each needs a `_denote` at
the environment the invariant fixes before its `WalkLink` can name its target.

The two `phi` values come out of that: `%inc.i` is bound by the *header*
(`while.body.i`, `%inc.i = %k.0.i249 + 1`), so at the merge it is `C.k + 1` and
`WalkInv.blockIndex` names it; `%sp.i.1` is the merge's own selection and
`WalkDispatch`'s `spOp`/`spv` name it at the predecessor.  The price premise is
`p + 2 ≤ 32·Δk + 8·ΔA` with `Δk = 1` and `ΔA` the entry's span, which is
`walkCredit_suffices` at the block count `p ≤ 22 + 6b` (`walkDispatchPrice`,
`walkScanStepWidth_le_byteAllowance`).

**The exit's tail.**  From `cleanup478.i` with the test false, the body reaches a
return in three or four blocks and on every path:

  `if.then485.i → if.end490.i → s2_walk.exit → if.end`
  `if.then485.i → if.end490.i → if.then492.i → if.then → if.end`
  `if.then485.i → if.then488.i → if.then → if.end`

`walkExitBlock_denote`, `walkIfThen_step` and `walkIfEnd_step` are the last three
blocks of those paths; the merge's *false* branch and `if.then485.i`,
`if.end490.i`, `if.then492.i`, `if.then488.i` are what is not yet run.  `WalkExit`
is stated at the head because the last entry's dispatch runs inside the exit
branch's credit (`walkPotential G C + 27`), so it is the dispatch's run followed by
this tail. -/

/-! ### The revolution, composed

The dispatch's segment, the merge's step and the header's pass.  The two `phi` runs
are the merge's own state (`cleanup478Out`), so no hypothesis sits between
`walkBack_step_at`'s invariant and `whileBody_step`'s premises. -/

/-- **One revolution is one segment.**  Its price is the dispatch's plus the two
steps, and the potential falls by the dispatch's spending because only the index
has moved: the merge sets the depth and resets the inner component, and the
header's pass carries the spans the dispatch decoded. -/
theorem WalkDispatch.revolution {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (hdisp : WalkDispatch calls G) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k + 1 < G.nep) :
    ∃ (C' : WalkCarry G) (s' : State) (p : Nat),
      WalkSegment calls G C s C' s' p ∧ C'.block = walkLoopHead ∧
      C.k < C'.k ∧ C'.k < G.nep ∧ p + walkPotential G C' ≤ walkPotential G C := by
  obtain ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, hseg, hblock, hkc, hpre,
    hspIn, hspV, hkIn, hkV, hnep, _hguard, hklt, hstrict, hspc, hspw, hpot⟩ :=
    hdisp C s hInv hhead hk
  obtain ⟨hstepB, hInvB, hrunB⟩ :=
    walkBack_step_at G Cd sd hseg.inv' hblock hpre hspIn hspV hkIn hkV hnep
      (by omega)
  obtain ⟨s', hstepH, hInvH, _hmono, hrunH⟩ :=
    whileBody_step (G := G)
      (C := { Cd with block := "while.body.i", inner := walkInnerCap G })
      (s := cleanup478Out sd spv k2) hInvB rfl (cleanup478Out_pre) (cleanup478Out_k)
      (cleanup478Out_sp) (by rw [hkc]; exact hstrict) hklt hspc hspw
  let C' : WalkCarry G :=
    { { Cd with block := "while.body.i", inner := walkInnerCap G } with
        block := walkLoopHead, k := k2, sp := spv }
  have hseg' : WalkSegment calls G C s C' s' (p + 1 + 1) :=
    { run := fun n => by
        rw [show p + 1 + 1 + n = p + (1 + (1 + n)) from by omega,
          hseg.run (1 + (1 + n)), hrunB (1 + n), hrunH n]
      inv' := hInvH }
  have hpot' : (p + 1 + 1) + walkPotential G C' ≤ walkPotential G C := by
    have hmono : entryPos G C.k ≤ entryPos G k2 :=
      entryPos_mono G (le_of_lt hstrict) hklt
    have hp : entryPos G C.k ≤ G.n := le_of_lt (entryPos_lt G (by omega))
    have hp' : entryPos G k2 ≤ G.n := le_of_lt (entryPos_lt G hklt)
    have hspend := walkPotential_spend (G := G) (C := C) (C' := C') (p := p + 2)
      (le_of_lt hstrict) (le_of_lt hklt) hp hp' hmono hpot
    simpa using hspend
  refine ⟨C', s', p + 1 + 1, hseg', rfl, ?_, ?_, ?_⟩
  · show C.k < k2
    exact hstrict
  · show k2 < G.nep
    exact hklt
  · exact hpot'

/-- **The loop's step, from the dispatch and the exit.**  The case split is the
entry index: while an entry is left after this one the dispatch runs and the
merge's test is clear, and at the last entry the test fails and the exit's tail
takes over. -/
theorem walkLoopStep_of_dispatch_exit {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {v : Value} (hdisp : WalkDispatch calls G) (hexit : WalkExit calls G v) :
    WalkLoopStep calls G v 27 := by
  intro C s hInv hhead hk
  by_cases hcase : C.k + 1 < G.nep
  · exact Or.inl (hdisp.revolution C s hInv hhead hcase)
  · exact Or.inr (hexit C s hInv hhead (by omega))

/-- **`F ≤ 27` is the finalisation allowance** at the seed's three steps: the
record's constant less the seed's prefix and the exit's own jump. -/
theorem walkExitFits (F : Nat) (hF : F ≤ 27) :
    3 + F + 2 ≤ stage2FinalisationAllowance := by
  unfold stage2FinalisationAllowance
  omega

/-! ### The geometry

`WalkGeom` is `stage2Pre` unpacked, and the completion's budget is a function of
the argument list, so the construction states the argument equation as well as the
structure: the completion at `a13` is the completion at the geometry's own numbers
(`walkCompletes_at_stage2Budget`). -/

/-- **`stage2Pre`'s witnesses are a `WalkGeom`.**  Field for field and clause for
clause, with the argument list the geometry's own numbers and the watermark's
cursor. -/
theorem walkGeom_at_pre {args : List Value} {m0 : Mem} {next : Nat}
    (h : Γ_stage2.pre args m0 next) :
    ∃ G : WalkGeom m0,
      G.next0 = next ∧
      args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] := by
  have h' : stage2Pre args m0 next := h
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, hargs, doc, tail, entries, order, inside, esc, arenaCap, arenaRoom,
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate, hwm, hnxp, hdstcap,
    hevcap, hbpos, hbLt, hepLt⟩ := h'
  refine ⟨{
    b := b
    n := n
    ep := ep
    nep := nep
    xp := xp
    nxp := nxp
    dst := dst
    dstcap := dstcap
    ndst := ndst
    ev := ev
    evcap := evcap
    nev := nev
    err := err
    bs := bs
    ent := ent
    ndst0 := ndst0
    nev0 := nev0
    doc := doc
    tail := tail
    entries := entries
    order := order
    inside := inside
    esc := esc
    arenaCap := arenaCap
    arenaRoom := arenaRoom
    evCap := evCap
    evRoom := evRoom
    ndstRead := ndstRead
    nevRead := nevRead
    errBytes := errBytes
    maxDoc := maxDoc
    nxpLt := hnxp
    dstcapLt := hdstcap
    evcapLt := hevcap
    bPos := hbpos
    bLt := hbLt
    epLt := hepLt
    separate := separate
    next0 := next
    watermark := hwm }, rfl, hargs⟩

/-- The geometry's document fits a word, so its length is its argument's value. -/
theorem WalkGeom.n_lt {m0 : Mem} (G : WalkGeom m0) : G.n < 2 ^ 64 := by
  have h := G.maxDoc
  simp only [stage2MaxDocument] at h
  omega

/-- The geometry's entry count fits a word: the stream's positions are inside the
document and strictly increasing. -/
theorem WalkGeom.nep_lt {m0 : Mem} (G : WalkGeom m0) : G.nep < 2 ^ 64 := by
  have h := G.nep_le
  have h' := WalkGeom.n_lt G
  omega

/-! ### The stage, and what its construction needs

`WalkStage` is the adapter's staging at the geometry.  `stage2StagedPre` supplies
the seven objects' presence, `%d.i`'s and the seventeen-object separation, and
`WalkStage`'s own clauses add the cursor the seven end at.  Building it is *not* the
definitional match the geometry is, and the two lemmas below are the part that is:
**the separation transports**, once the numbers agree.

`walkDisjoint_drop_member` drops `%d.i`'s entry from the staged list — the one
structural difference between the two region lists, since `stage2StagedPre` inserts
it between the seventeen walk regions and the caller's two count slots while
`WalkStage.separate` names the seventeen without it — and `walkDisjoint_before`
reads the half of `WalkStage.dSep` the staging's order carries.  So the separation
algebra is not what the construction owes.

What it owes is the *numbers*, and they are not free:

* `stage2StagedPre` names its columns as words (`n nep nxp dstcap evcap` are
  `BitVec 64`) and its region list at their `.toNat`s, while `WalkGeom` carries the
  `Nat`s the ABI's argument list holds.  The two agree only inside the words, so
  the construction needs the 64-bit width facts.  The precondition now states them
  (`nxp`, `dstcap`, `evcap` as its last three clauses; `n` is bounded by
  `maxDoc` and `nep` by the stream's order), so they are the geometry's
  (`WalkGeom.nxpLt` and its two siblings) rather than a gap between two records:
* the arena entry's extent names the cursor *value* — `G.ndst0`, which is
  `stage2Pre`'s read of the slot — while the adapter's staging names its own read of
  the same slot (`stage2StagedPre`'s `ndst0`).  Both predicates read
  `readBytes mem ndst 8`, so the two witnesses agree modulo `2 ^ 64`
  (`wordBytes8_mod_eq`), and the staged predicate's cursor-width clause makes each
  of them the word's value; the equation is therefore arithmetic rather than a
  hypothesis;
* `WalkStage.sevenEnd` bounds the seven nested objects by the caller's cursor.
  `stage2Pre`'s watermark is stated at the thirteen ABI objects only, so the
  adapter's predicate carries the same clause at the seven it names
  (`stage2StagedPre`'s last conjunct).  It is what makes the root slot fresh of the
  log and the event stream (`WalkStage.rootSlot_log`, `WalkStage.rootSlot_ev`).

So premise 4 is a construction on both halves: the geometry is `walkGeom_at_pre`,
and the stage is `walkStage_at_pre` — these two lemmas, the adapter's two number
clauses, and the staged list's own cross half.  Nothing in it is a hypothesis beside
the record's precondition and the adapter's staging, which is what `walkPremises_of_parts`
uses to state the remaining premises at a pair the prover is given.
-/

/-- **A separated list stays separated when an inserted member is dropped.**  The
staged list has `%d.i` inserted between the seventeen walk regions and the
caller's two count slots; `WalkStage.separate` names the list without it. -/
theorem walkDisjoint_drop_member {L slots : List (Nat × Nat)} {d : Nat}
    (h : DisjointRegions ((L ++ [(d, 8)]) ++ slots)) : DisjointRegions (L ++ slots) := by
  unfold DisjointRegions at h ⊢
  rw [List.pairwise_append] at h
  obtain ⟨hL, hslots, hcross⟩ := h
  rw [List.pairwise_append] at hL
  obtain ⟨hLp, -, -⟩ := hL
  refine (List.pairwise_append).2 ⟨hLp, hslots, ?_⟩
  intro a ha b hb
  exact hcross a (List.mem_append_left _ ha) b hb

/-- **Every walk region ends at or before the inserted member**, which is the half
of `WalkStage.dSep` the staging's order carries. -/
theorem walkDisjoint_before {L slots : List (Nat × Nat)} {d n : Nat}
    (h : DisjointRegions ((L ++ [(d, n)]) ++ slots)) :
    ∀ r ∈ L, r.1 + r.2 ≤ d ∨ d + n ≤ r.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨hL, -, hcross⟩ := h
  rw [List.pairwise_append] at hL
  obtain ⟨-, -, hcrossL⟩ := hL
  intro r hr
  exact hcrossL r hr (d, n) (by simp)

/-! ### The stage's columns, reconciled

`stage2StagedPre` names the ABI's five numbers as 64-bit words and its regions at
those words' `.toNat`s, while `WalkGeom` carries the precondition's `Nat`s — the
numbers the argument list is built from.  The two are the same numbers only when
each is the word's value, i.e. below `2 ^ 64`.

Three of the five follow from the precondition's own clauses: `n` from the
document's bound (`stage2MaxDocument`, `2 ^ 32`) and `nep` from the stream's order
(`WalkGeom.nep_le`).  `nxp`, `dstcap` and `evcap` do not: the precondition states
lower bounds on them (`HasBytes mem xp (4 * nxp)`, `ndst0 + n + reserve ≤ dstcap`,
`nev0 + 13 * n ≤ evcap`) beside the three widths the pre now states, which is also what the
record's **post** asserts (`stage2Boundary`).  The cursor slot is the fourth: the
staged predicate reads `readBytes mem ndst 8` and the precondition reads the same
eight bytes, so the two values agree modulo the word and agree outright once both
are written below it.

So the reconciliation is arithmetic, and its hypotheses are the two predicates'
clauses rather than a proof gap: `stage2StagedRegions_reconcile` is the whole of
"the numbers do not agree", stated at the two argument equations and the widths.
What is left once it holds is `walkDisjoint_drop_member` and `walkDisjoint_before`
above, and the cursor clause `WalkStage.sevenEnd`, which is the adapter's own
watermark at the seven.  `walkStage_at_pre` is that composition. -/

/-- **A slot word decides its value modulo its width.**  Two numbers whose eight
little-endian bytes agree are congruent modulo `2 ^ 64`, which is the whole of what
a slot read says about the cursor it encodes. -/
theorem wordBytes8_mod_eq {x y : Nat} (h : wordBytes 8 x = wordBytes 8 y) :
    x % 2 ^ 64 = y % 2 ^ 64 := by
  have h' := congrArg bytesToNat h
  simpa only [wordBytes, natToBytes_toNat,
    show (256 : Nat) ^ 8 = 2 ^ 64 from by decide] using h'

/-- **The argument list determines its thirteen components.**  Two readings of one
list at the ABI's thirteen slots name the same document, streams, slots and
counts, and each of the five numbers the list carries as a word is that word's
value — the direction the staged predicate's regions need, since they are stated at
the words' `.toNat`s. -/
theorem stage2Args_components {args : List Value}
    {b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat}
    {b' xp' dst' ev' ep' ndst' nev' err' : Nat}
    {nw nepw nxpw dstcapw evcapw : BitVec 64}
    (h13 : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
      .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err])
    (hst : args = [.ptr b', .int 64 nw, .ptr ep', .int 64 nepw, .ptr xp',
      .int 64 nxpw, .ptr dst', .int 64 dstcapw, .ptr ndst', .ptr ev',
      .int 64 evcapw, .ptr nev', .ptr err']) :
    b = b' ∧ nw = BitVec.ofNat 64 n ∧ ep = ep' ∧ nepw = BitVec.ofNat 64 nep ∧
      xp = xp' ∧ nxpw = BitVec.ofNat 64 nxp ∧ dst = dst' ∧
      dstcapw = BitVec.ofNat 64 dstcap ∧ ndst = ndst' ∧ ev = ev' ∧
      evcapw = BitVec.ofNat 64 evcap ∧ nev = nev' ∧ err = err' := by
  have hm : ([.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
      .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] : List LeanLLVM.Value) =
    [.ptr b', .int 64 nw, .ptr ep', .int 64 nepw, .ptr xp', .int 64 nxpw,
      .ptr dst', .int 64 dstcapw, .ptr ndst', .ptr ev', .int 64 evcapw,
      .ptr nev', .ptr err'] := h13.symm.trans hst
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq] at hm
  obtain ⟨hb, hw1, hep, hw2, hxp, hw3, hdst, hw4, hndst, hev, hw5, hnev, herr⟩ := hm
  exact ⟨hb, (eq_of_heq hw1).symm, hep, (eq_of_heq hw2).symm, hxp,
    (eq_of_heq hw3).symm, hdst, (eq_of_heq hw4).symm, hndst, hev,
    (eq_of_heq hw5).symm, hnev, herr⟩

/-- **The adapter's staged list is the walk's own region list**, once the columns
agree: the two argument readings name the same thirteen objects, the three free
widths make `nxp`, `dstcap` and `evcap` their words' values, and the cursor slot's
two reads make the staged cursor the precondition's.  This is the equality
`WalkStage.separate` is drawn from — the staged predicate's list at its witnesses,
which is the walk's list at the geometry's numbers. -/
theorem stage2StagedRegions_reconcile {args : List Value}
    {b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat}
    {b' xp' dst' ev' ep' ndst' nev' err' : Nat}
    {nw nepw nxpw dstcapw evcapw : BitVec 64}
    {ndst0 ndst0' : Nat}
    (h13 : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
      .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err])
    (hst : args = [.ptr b', .int 64 nw, .ptr ep', .int 64 nepw, .ptr xp',
      .int 64 nxpw, .ptr dst', .int 64 dstcapw, .ptr ndst', .ptr ev',
      .int 64 evcapw, .ptr nev', .ptr err'])
    (hn : n < 2 ^ 64) (hnep : nep < 2 ^ 64) (hnxp : nxp < 2 ^ 64)
    (hdstcap : dstcap < 2 ^ 64) (hevcap : evcap < 2 ^ 64)
    (hndst0 : ndst0 < 2 ^ 64) (hndst0' : ndst0' < 2 ^ 64)
    (hmod : ndst0 % 2 ^ 64 = ndst0' % 2 ^ 64)
    (c ctype cst tok s z e nkSlot nxpSlot : Nat) :
    stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
        c ctype cst tok s z e =
      stage2WalkRegions b' nw.toNat ep' nepw.toNat xp' nxpw.toNat dst' ndst0' ev'
        evcapw.toNat ndst' nev' err' c ctype cst tok s z e := by
  obtain ⟨hb, hw1, hep, hw2, hxp, hw3, hdst, hw4, hndst, hev, hw5, hnev, herr⟩ :=
    stage2Args_components h13 hst
  have hnd : ndst0 = ndst0' := by
    have h1 : ndst0' % 2 ^ 64 = ndst0' := Nat.mod_eq_of_lt hndst0'
    have h2 : ndst0 % 2 ^ 64 = ndst0 := Nat.mod_eq_of_lt hndst0
    omega
  rw [hb, hw1, hep, hw2, hxp, hw3, hdst, hndst, hev, hw5, hnev, herr, ← hnd]
  simp only [stage2WalkRegions, stage2Regions, stage2StagedWrites, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hnep, Nat.mod_eq_of_lt hnxp,
    Nat.mod_eq_of_lt hdstcap, Nat.mod_eq_of_lt hevcap]

/-! ### The stage, constructed

`WalkPremises` used to hand the completion a geometry *and* a staging, and the two
preconditions were enough to build only the first (`walkGeom_at_pre`).  The stage is
a construction too, and the two clauses the adapter's predicate gained are what make
it one: the width facts reconcile the adapter's columns with the geometry's
(`stage2StagedRegions_reconcile`), the cursor slot's width makes the two readings of
that slot one number, and the seven's watermark is `WalkStage.sevenEnd`.  So a caller
inside the record's domain has the walk's staging, and premise 4 no longer assumes
anything the record does not grant. -/

/-- **The adapter's staging is the walk's `WalkStage`.**  The seventeen-object
separation is the staged list with `%d.i`'s entry dropped
(`walkDisjoint_drop_member`), after the reconcile transports the staged list's
numbers to the geometry's; the seven objects' presence and `%d.i`'s are the staged
predicate's two presence clauses; `%d.i`'s separation is the staged list's cross
half, read at the geometry's numbers; and the seven's end is the adapter's
watermark at the call's cursor. -/
theorem walkStage_at_pre {args : List Value} {m0 : Mem} {next : Nat}
    {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hpre : Γ_stage2.pre args m0 next)
    (hst : stage2StagedPre args m0 next d c ctype cst tok s z e nkSlot nxpSlot) :
    ∃ (G : WalkGeom m0) (S : WalkStage G), G.next0 = next ∧
      args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] := by
  obtain ⟨G, hnext, hargs⟩ := walkGeom_at_pre hpre
  obtain ⟨hpres, hd8, b', nw, ep', nepw, xp', nxpw, dst', dstcapw, ndst0', ev', evcapw,
    ndst', nev', err', hargs', hread', hdisj', hndst0w, hwm'⟩ := hst
  -- the argument list names one set of objects, read at the ABI's words and again
  -- at the adapter's: the two readings' slot addresses agree, and so does the rest
  obtain ⟨-, -, -, -, -, -, -, -, hndstEq, -, -, -, -⟩ :=
    stage2Args_components hargs hargs'
  -- the two cursor witnesses are one word, so they are one number
  have hmod : G.ndst0 % 2 ^ 64 = ndst0' % 2 ^ 64 := by
    have hreadG : readBytes m0 ndst' 8 = some (wordBytes 8 G.ndst0) := by
      rw [← hndstEq]; exact G.ndstRead
    exact wordBytes8_mod_eq (Option.some.inj (hreadG.symm.trans hread'))
  have hGndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  -- the two region lists are one list, at the geometry's numbers
  have hrecon := stage2StagedRegions_reconcile hargs hargs' (WalkGeom.n_lt G)
    (WalkGeom.nep_lt G) G.nxpLt G.dstcapLt G.evcapLt hGndst0 hndst0w hmod
    c ctype cst tok s z e nkSlot nxpSlot
  have hdisjG : DisjointRegions
      ((stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
          G.ndst G.nev G.err c ctype cst tok s z e ++ [(d, 8)]) ++
        [(nkSlot, 8), (nxpSlot, 8)]) := by
    rw [← hrecon] at hdisj'
    simpa only [stage2StagedRegions, List.append_assoc] using hdisj'
  refine ⟨G, ?_, hnext, hargs⟩
  refine ⟨c, ctype, cst, tok, s, z, e, nkSlot, nxpSlot, ?_, hpres, d, hd8, ?_, ?_⟩
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

/-! ### The completion at the ABI's arguments -/

/-- **What a dispatch supplies, and nothing else.**  At every staging the record
admits: a geometry whose numbers are the argument list's and a staging of the
walk's own objects — both now constructed (`walkGeom_at_pre`, `walkStage_at_pre`,
and `walkPremises_of_parts` reads this definition at the pair they give) — the
seed's three-step prefix to the loop head, the invariant there, and the loop's step
at the value the exit returns (`WalkDispatch` beside `WalkExit`). -/
def WalkPremises (sub : Calls) (d c ctype cst tok s z e nkSlot nxpSlot : Nat) : Prop :=
  ∀ (a13 : List Value) (mem : Mem) (next : Nat),
    Γ_stage2.pre a13 mem next →
    stage2StagedPre a13 mem next d c ctype cst tok s z e nkSlot nxpSlot →
    ∃ (m0 : Mem) (G : WalkGeom m0) (S : WalkStage G),
      G.next0 = next ∧
      a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] ∧
      0 < G.nep ∧
      (∀ n, runFuel (stage2Calls sub) (3 + n) stage2Body
          (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
        runFuel (stage2Calls sub) n stage2Body
          (walkSeedFinalState G S
            (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
            (entryPos G 0) (entryByte G 0))) ∧
      WalkInv G (walkSeed G S)
        (walkSeedFinalState G S
          (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
          (entryPos G 0) (entryByte G 0)) ∧
      (∃ v : Value, WalkLoopStep (stage2Calls sub) G v 27)

/-- **What a dispatch supplies, at the geometry and the stage the record gives.**
A proof of `WalkPremises` no longer has to invent a geometry and a staging: the two
constructions (`walkGeom_at_pre`, `walkStage_at_pre`) build them from the record's
precondition and the adapter's staging, so the seed's prefix, the invariant at the
loop head and the loop's step are owed at a pair the prover *is given*.  This is the
shape the dispatch's proof is written against, and it is why the two constructions
are theorems rather than fields of the premise. -/
theorem walkPremises_of_parts {d c ctype cst tok s z e nkSlot nxpSlot : Nat} {sub : Calls}
    (h : ∀ (a13 : List Value) (mem : Mem) (next : Nat) (G : WalkGeom mem)
        (S : WalkStage G),
      Γ_stage2.pre a13 mem next →
      stage2StagedPre a13 mem next d c ctype cst tok s z e nkSlot nxpSlot →
      G.next0 = next →
      a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] →
      0 < G.nep ∧
      (∀ n, runFuel (stage2Calls sub) (3 + n) stage2Body
          (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
        runFuel (stage2Calls sub) n stage2Body
          (walkSeedFinalState G S
            (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
            (entryPos G 0) (entryByte G 0))) ∧
      WalkInv G (walkSeed G S)
        (walkSeedFinalState G S
          (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
          (entryPos G 0) (entryByte G 0)) ∧
      (∃ v : Value, WalkLoopStep (stage2Calls sub) G v 27)) :
    WalkPremises sub d c ctype cst tok s z e nkSlot nxpSlot := by
  intro a13 mem next hpre hst
  obtain ⟨G, S, hnext, hargs⟩ := walkStage_at_pre hpre hst
  obtain ⟨hn, hseed, hInv, hloop⟩ := h a13 mem next G S hpre hst hnext hargs
  exact ⟨mem, G, S, hnext, hargs, hn, hseed, hInv, hloop⟩

/-- **The completion at the record's own budget**, from the premises the four
obstructions name: the seed's prefix at the ABI's entry state, the invariant at the
loop head, and the loop's step.  The budget is `stage2Budget` at `a13`, which
`walkGeom_at_pre` identifies with the geometry's numbers. -/
theorem stage2WalkCompletes_of_premises {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    {sub : Calls} (h : WalkPremises sub d c ctype cst tok s z e nkSlot nxpSlot) :
    Stage2WalkCompletes d c ctype cst tok s z e nkSlot nxpSlot sub := by
  intro a13 mem next hpre hstaged
  obtain ⟨m0, G, S, hnext, hargs, hn, hseed, hInv, hloop⟩ :=
    h a13 mem next hpre hstaged
  obtain ⟨v, hloopv⟩ := hloop
  obtain ⟨v', m, hrun⟩ :=
    walkCompletes_at_stage2Budget (calls := stage2Calls sub) (G := G)
      (C := walkSeed G S)
      (s := walkSeedFinalState G S
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
        (entryPos G 0) (entryByte G 0))
      (sEntry := EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
      (v := v) (j := 3) (F := 27) (b := G.b) (ep := G.ep) (xp := G.xp) (dst := G.dst)
      (dstcap := G.dstcap) (ndst := G.ndst) (ev := G.ev) (evcap := G.evcap)
      (nev := G.nev) (err := G.err) (nxp := G.nxp)
      hseed hInv (walkSeed_block G S)
      (by simp only [walkSeed]; exact hn) hloopv (walkExitFits 27 (Nat.le_refl 27))
      (WalkGeom.n_lt G) (WalkGeom.nep_lt G)
  refine ⟨v', m, ?_⟩
  rw [hargs] at hrun ⊢
  rw [show stage2Budget
      [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] mem
    = stage2Budget
      [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] m0 from rfl]
  exact hrun

/-- **The obligation from the premises and its post.**  `Stage2WalkObligation` is
the completion conjunct beside the post (`stage2WalkObligation_iff_completion`), so
a dispatch that supplies `WalkPremises` and the record's post rule has the
obligation.  Naming the two is the point: the completion is this module's, and the
post half — the run's own region claim at the outcome — is not read here. -/
theorem stage2WalkObligation_of_premises {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    {sub : Calls} (h : WalkPremises sub d c ctype cst tok s z e nkSlot nxpSlot)
    (hpost : ∀ args mem next,
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).pre args mem next →
      ∀ o, BehFromState (stage2Calls sub) stage2Body
          (EntryState stage2Body args mem next) o →
        (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post args mem next o) :
    JsonStage2IR.Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot sub :=
  (stage2WalkObligation_iff_completion d c ctype cst tok s z e nkSlot nxpSlot sub).2
    ⟨stage2WalkCompletes_of_premises h, hpost⟩

/-! ### The revolution's counted credit

The census measured the dispatch's two numbers: at most twenty-two blocks on an
entry's own path (`walkDispatchPrice`), and at most six blocks per document byte a
scan visits (`walkScanStepSets`' widest set).  An entry of `b` bytes therefore costs
at most `22 + 6 * b` model control steps, and the credit the revolution consumes is
`32 + 8 * b` — one entry allowance plus one byte allowance per byte the entry spans
(`walkPotential_spend`).  The inequality holds at every width:

  `22 + 6b + 2 ≤ 32 + 8b`.

The direction the credit form repairs is the other one.  Charging the *decoded*
extents asked the price to fit after the newly decoded bytes were charged —
`22 + 6b + 2 + 8b ≤ 32` — which fails from the first byte on, so no entry containing
a string could satisfy it and the premise had no producer.  `walkCreditOldOk` is
that form, and the guard below is its falsity at the acceptance's rows. -/

/-- **The blocks the dispatch's trace can visit.**  Reachable from the head without
passing the merge that closes the iteration: the switch's branch is the token's, so
a proof must cover every branch, and this set — not `walkDispatchPrice`'s longest
path — is what a dispatch's run is written over.  The four trap blocks are in it
(`walkTrap_noStep`: they have no step), and so are the five scan latches, whose
links are named for the edge they close. -/
def walkDispatchReach : List String :=
  let rec go (fuel : Nat) (seen : List String) (frontier : List String) : List String :=
    match fuel with
    | 0 => seen
    | fuel + 1 =>
      match frontier with
      | [] => seen
      | b :: rest =>
        if seen.contains b || b = "cleanup478.i" then go fuel seen rest
        else go fuel (b :: seen) (rest ++ (walkSucc b).filter (fun u => !seen.contains u))
  go 400 [] ["NodeBlock21"]

#guard walkDispatchReach.length = 156

#guard walkDispatchReach.eraseDups.length = walkDispatchReach.length

#guard walkDispatchReach.all (fun n => (stage2Body.findBlock n).isSome) = true

#guard walkDispatchReach.contains "cleanup478.i" = false

/-- The dispatch's counted price fits the credit it consumes, at every entry width:
twenty-two blocks and six per byte against thirty-two and eight. -/
theorem walkCredit_suffices (b : Nat) : 22 + 6 * b + 2 ≤ 32 + 8 * b := by omega

/-- The acceptance's rows, at their counted numbers: `(scenario, blocks the
dispatch traverses, bytes the entry spans)`. -/
def walkCreditRows : List (String × Nat × Nat) :=
  [("long string", 22 + 6 * 100, 100),
   ("escaped string", 22 + 6 * 96, 96),
   ("whitespace-heavy", 22 + 6 * 80, 80),
   ("malformed late", 22 + 6 * 64 + 4, 64),
   ("the last entry's exit", 22 + 6 * 100 + 5, 100)]

/-- Every row's price fits `32·Δk + 8·ΔA` at `Δk = 1`. -/
def walkCreditOk (r : String × Nat × Nat) : Bool :=
  r.2.1 + 2 ≤ 32 + 8 * r.2.2

#guard walkCreditRows.all walkCreditOk

/-- The form the credit replaced, at the same rows: the price had to fit inside
`32` *after* the newly decoded bytes were charged. -/
def walkCreditOldOk (r : String × Nat × Nat) : Bool :=
  r.2.1 + 2 + 8 * r.2.2 ≤ 32

#guard !walkCreditRows.any walkCreditOldOk

/-- The hundred-byte long-string revolution, counted: 624 steps against a credit of
832. -/
theorem walkCredit_long_string :
    (22 + 6 * 100 + 2 : Nat) = 624 ∧ (32 + 8 * 100 : Nat) = 832 ∧ 624 ≤ 832 := by
  decide

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cleanup478Out_k
#print axioms LeanLLVM.Refinement.WalkScope.cleanup478Out_sp
#print axioms LeanLLVM.Refinement.WalkScope.walkBack_step_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkDispatch.revolution
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStep_of_dispatch_exit
#print axioms LeanLLVM.Refinement.WalkScope.walkExitFits
#print axioms LeanLLVM.Refinement.WalkScope.walkGeom_at_pre
#print axioms LeanLLVM.Refinement.WalkScope.wordBytes8_mod_eq
#print axioms LeanLLVM.Refinement.WalkScope.stage2Args_components
#print axioms LeanLLVM.Refinement.WalkScope.stage2StagedRegions_reconcile
#print axioms LeanLLVM.Refinement.WalkScope.walkCredit_suffices
#print axioms LeanLLVM.Refinement.WalkScope.walkCredit_long_string
#print axioms LeanLLVM.Refinement.WalkScope.walkDisjoint_drop_member
#print axioms LeanLLVM.Refinement.WalkScope.walkDisjoint_before
#print axioms LeanLLVM.Refinement.WalkScope.WalkGeom.n_lt
#print axioms LeanLLVM.Refinement.WalkScope.WalkGeom.nep_lt
#print axioms LeanLLVM.Refinement.WalkScope.walkStage_at_pre
#print axioms LeanLLVM.Refinement.WalkScope.walkPremises_of_parts
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkCompletes_of_premises
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkObligation_of_premises

end WalkScope

end LeanLLVM.Refinement
