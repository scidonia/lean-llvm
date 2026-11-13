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

What the module does not do is inhabit `Stage2WalkObligation`: the loop step's two
premises are the census's dispatch chain and the exit's tail, and the post half is
untouched here.  The premises are stated, not assumed away, and
`WalkPremises`/`stage2WalkCompletes_of_premises` is the exact shape of what a
dispatch supplies.

The seed's residue is not a trace and is enumerated rather than assumed.  The three
block runs `walkSeedPrefix_runFuel` takes are `entry`'s fifty-seven instructions
(`walkEntry_denote`), `while.body.i.lr.ph`'s five `getelementptr`s
(`walkPreheader_denote`) and `while.body.i`'s first pass
(`whileBodyFirst_denote`), plus the entry test's bit and the header's two loads.
`walkEntry_denote`'s hypothesis list is what the residue is made of, and every item
in it is one of four kinds: the eighteen register bindings, which are
`EntryState`'s own argument list read at `stage2Body.params`; five region-separation
facts, which are `WalkStage.separate` at the two cursor slots; the two cursor-slot
reads, which are the geometry's `ndstRead`/`nevRead`; and the word facts the two
preconditions do not state — `0 < G.b`, `G.b < 2^64`, `G.ep < 2^64`, and the counts
`G.nxp`, `G.dstcap`, `G.evcap`, `G.ndst0`, `G.nev0` inside their words.  The last
family is the same one the stage's construction owes (§ *The stage*), and it is what `Stage2Run`
asserts of the *report* (`nxpLt`, `dstcapLt`, `evcapLt`, `nepLt`): the record's post
demands a width its precondition leaves free.  So the seed's three runs are address
facts and environment reads, not a trace — which is why the four premises reduce to
the dispatch's chain and the exit's tail once the widths are stated.
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
the stream, a depth inside the stacks, and a price inside the iteration's
allowance: the dispatch's own count plus the merge's and the header's two steps,
against `walkPotential`'s fall at `k2`.  The two steps are named in the premise
because they are steps the revolution takes and the potential does not pay for
separately: one iteration's price is one entry allowance (`stage2EntryAllowance`,
`32`) and the merge and the header are the last two of the dispatch's blocks in
that allowance. -/
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
      p + 2 + walkPotential G { Cd with k := k2, sp := spv } ≤ walkPotential G C

/-- **The exit**: at the head whose merge fails its test (`C.k + 1 = G.nep`, so
`%inc.i` is the entry count), `27` steps reach a state whose jump is followed by a
return.  The `27` is the finalisation allowance less the seed's three steps and
the two terminal ones (`walkExitFits`). -/
def WalkExit (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (v : Value) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 = G.nep →
    ∃ (q : Nat) (s1 s2 sret : State),
      q ≤ 27 ∧
      (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
      step calls stage2Body s1 = .jump s2 ∧
      step calls stage2Body s2 = .ret v sret

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
  have hpot' : walkPotential G C' = walkPotential G { Cd with k := k2, sp := spv } := rfl
  refine ⟨C', s', p + 1 + 1, hseg', rfl, ?_, ?_, ?_⟩
  · show C.k < k2
    exact hstrict
  · show k2 < G.nep
    exact hklt
  · rw [hpot']
    omega

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
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate, hwm⟩ := h'
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
  the construction needs the 64-bit width facts — and `Γ_stage2.pre` states none of
  them, while `Stage2Run`'s `nepLt`/`nxpLt`/`dstcapLt`/`evcapLt` assert them of the
  *report*.  That is a contract gap rather than a construction step: the record's
  post demands widths its precondition leaves free;
* the arena entry's extent names the cursor *value* — `G.ndst0`, which is
  `stage2Pre`'s read of the slot — while the adapter's staging names its own read of
  the same slot (`stage2StagedPre`'s `ndst0`).  Nothing relates the two witnesses:
  both predicates read `readBytes mem ndst 8` and neither states the value, so a
  construction either takes the equation as a hypothesis or proves `natToBytes`
  injective at both values' widths;
* `WalkStage.sevenEnd` bounds the seven nested objects by the caller's cursor.
  `stage2StagedPre` separates the seven but says nothing about where they end, and
  `stage2Pre`'s watermark is stated at the thirteen ABI objects only, so this is a
  staging fact the adapter must state.  It is what makes the root slot fresh of the
  log and the event stream (`WalkStage.rootSlot_log`, `WalkStage.rootSlot_ev`).

So premise 4 has one constructive half and one that is a caller's clause: the
geometry is `walkGeom_at_pre`, and the stage is these two lemmas plus a staging
predicate that states the widths, the cursor and the watermark at the seven.
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

/-! ### The completion at the ABI's arguments -/

/-- **What a dispatch supplies, and nothing else.**  At every staging the record
admits: a geometry whose numbers are the argument list's
(`walkGeom_at_pre`), the seed's three-step prefix to the loop head and the
invariant there (the seed's caller facts), and the loop's step at the value the
exit returns (`WalkDispatch` beside `WalkExit`). -/
def WalkPremises (sub : Calls) (d c ctype cst tok s z e nkSlot nxpSlot : Nat) : Prop :=
  ∀ (a13 : List Value) (mem : Mem) (next : Nat),
    Γ_stage2.pre a13 mem next →
    stage2StagedPre a13 mem d c ctype cst tok s z e nkSlot nxpSlot →
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

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cleanup478Out_k
#print axioms LeanLLVM.Refinement.WalkScope.cleanup478Out_sp
#print axioms LeanLLVM.Refinement.WalkScope.walkBack_step_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkDispatch.revolution
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStep_of_dispatch_exit
#print axioms LeanLLVM.Refinement.WalkScope.walkExitFits
#print axioms LeanLLVM.Refinement.WalkScope.walkGeom_at_pre
#print axioms LeanLLVM.Refinement.WalkScope.walkDisjoint_drop_member
#print axioms LeanLLVM.Refinement.WalkScope.walkDisjoint_before
#print axioms LeanLLVM.Refinement.WalkScope.WalkGeom.n_lt
#print axioms LeanLLVM.Refinement.WalkScope.WalkGeom.nep_lt
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkCompletes_of_premises
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkObligation_of_premises

end WalkScope

end LeanLLVM.Refinement
