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

The seed's run is not a residue any more.  `JsonStage2WalkSeedAtEntry` discharges
every hypothesis `walkSeedPrefix_runFuel` takes at the state the record starts
from: the entry block's environment is `stage2Args`'s list (`walkEntryState_env`),
the entry run's own hypothesis list is the argument list read at `stage2Body.params`
plus `WalkStage.separate`'s five separations at the two cursor slots, the two
cursor-slot reads and the word facts the geometry carries; the preheader and the
header's first pass are their own `_denote` results; the two loads the header takes
are the geometry's (`walkSeedPrefix_entry_geometry`), transported across the one
eight-byte cursor store the header makes; and the state the three blocks leave is
`walkSeedFinalState` field for field — the environment `walkSeedFinalEnv`, the
memory `walkEntryMem`, and the cursor's `next + 28` (the four `alloca`s
`stage2AllocaWrites` names).

One hypothesis is *not* discharged and is not a residue of this file: the entry
block calls `s2_init`, and `walkEntry_denote` is stated at
`stage2Calls stage2SubCalls`.  So the seed's run is proved at the reference call
selection, while `WalkPremises`'s seed conjunct is stated at `stage2Calls sub` for
the arbitrary `sub` the record's obligation names.  Passing between the two is the
first block's helper contract — what the selection's `s2_init` returns — and it is
the walk's first read of `sub`, not a fact about the pinned text.
-/
import LeanLLVM.Refinement.JsonStage2WalkPure
import LeanLLVM.Refinement.JsonStage2WalkSeedAtEntry
import LeanLLVM.Refinement.JsonStage2WalkSeedRun
import LeanLLVM.Refinement.JsonStage2WalkTraverse

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
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

/-- **The merge's failing test.**  The same two `phi` selections as the back edge,
with the test clear: `%cmp.i` is `0` and the terminator takes its false arm, so one
step lands at `if.then485.i` — the exit tail's first block — rather than at
`while.body.i`.  The index's width is a hypothesis because the comparison's value is
the word's: `nep ≤ k2` decides it only when `k2` is a word.

The test is `%k.2.i < %nep` (`cleanup478Block`'s `icmp ult`), so the clear case is
`nep ≤ k2` — at the exit the merge selects the entry count itself, which is why
`WalkExit` states its guard as `C.k + 1 = G.nep`. -/
theorem walkBackFalse_step {calls : Calls} (s : State) {p : String}
    {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpc : s.pc = "cleanup478.i") (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hk2 : k2 < 2 ^ 64) (hguard : nepv.toNat ≤ k2) :
    step calls stage2Body s =
      .jump { (((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (0 : BitVec 1))) with
        pc := "if.then485.i", pre := some "cleanup478.i" } := by
  have hult0 : evalICmp .ult (BitVec.ofNat 64 k2) nepv = (0 : BitVec 1) := by
    have hlt : ¬ (BitVec.ofNat 64 k2).toNat < nepv.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2]
      omega
    rw [show evalICmp .ult (BitVec.ofNat 64 k2) nepv
          = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 k2) nepv) from rfl]
    rw [show BitVec.ult (BitVec.ofNat 64 k2) nepv = false from by
      cases h : BitVec.ult (BitVec.ofNat 64 k2) nepv with
      | false => rfl
      | true => exact absurd ((BitVec.ult_iff_toNat_lt).1 h) hlt]
    rfl
  have hsel : PhiSelects s p
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }]
      [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
       ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] :=
    PhiSelects.cons hsp hspv (PhiSelects.cons hk hkv PhiSelects.nil)
  have hspecs : cleanup478Block.instrs =
      ([{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
        { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }].map
          PhiSpec.instr) ++
        [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
          (Operand.reg "%nep")] := by
    simp [cleanup478Block, PhiSpec.instr]
  have hden : denoteCode calls cleanup478Block.instrs s =
      some (((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (0 : BitVec 1))) := by
    rw [hspecs, denoteCode_phiRun (specs :=
        [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
         { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }])
        (vs := [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
                ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))])
        (rest := [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
          (Operand.reg "%nep")]) hpre hsel (by rfl)]
    rw [show s.bindAll [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
          ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] =
        LeanLLVM.Refinement.BlockEval.stateAt
          (("%k.2.i", .int 64 (BitVec.ofNat 64 k2)) ::
            ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)) :: s.env) s from rfl]
    rw [denoteCode_icmp_ult_reg (x := BitVec.ofNat 64 k2) (y := nepv)
      calls _ s "%cmp.i" "%k.2.i" "%nep"
      (by simp only [lookupName_cons_self])
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hnep)
      []]
    rw [hult0]
    rfl
  have hterm : cleanup478Block.term =
      Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" := rfl
  have hfind : stage2Body.findBlock s.pc = some cleanup478Block := by
    rw [hpc, cleanup478_find]
  simp only [step, hfind, hden, hterm]
  dsimp only [State.bind]
  simp only [execTerm, evalOperand, lookupName_cons_self, hpc]
  simp

/-- A one-bit value is zero or one: every `icmp` the tail tests is a `BitVec 1`, so
the two arms below are exhaustive and a step stated with the bit's `if` covers
both. -/
theorem walkBitVec1_zero_or_one (b : BitVec 1) : b = 0 ∨ b = 1 := by
  revert b
  decide

/-- **A `condbr` on a `BitVec 1` cell is the two-arm jump.**  `execTerm` carries a third
arm — `ub` — for a bit that is neither `0` nor `1`, and an `icmp`'s value never is, so
that arm is dead.  The shapes state their bit as a hypothesis for exactly this reason,
and this is the lemma that consumes it: with the bit in hand the terminator is one `if`,
which is the form every chain step's target is stated in.

It is a lemma rather than a per-goal tactic because every chain step over a `condbr`
needs it — the latch chain, the other four paths, and the scan inductions' exits. -/
theorem execTerm_condbr_bit {s : State} {c : Operand} {t f : String} {bit : BitVec 1}
    (hv : evalOperand s c = some (.int 1 bit)) (hb : bit = 0 ∨ bit = 1) :
    execTerm s (Term.condbr c t f) =
      .jump { s with pc := (if bit = 1 then t else f), pre := some s.pc } := by
  simp only [execTerm, hv]
  rcases hb with rfl | rfl <;> simp

/-- `cond.end349.i`'s successor at the writes its run leaves: the bound's cell, the
compare's cell, the token's two stores, and the arm the compare picks.  A flat `State`
literal, because the target has to be nameable without a nested `with`. -/
def condEnd349OutAt (s : State) (c ix : BitVec 64) (tk gap : Nat) : State :=
  { env := cells [("%cmp355.i", .int 1 (evalICmp .ugt c ix)),
      ("%cond350.i", .int 64 c)] s.env
    mem := writeBytes (writeBytes s.mem tk (natToBytes ix.toNat 8)) gap
      (natToBytes (BitVec.ofNat 32 1).toNat 4)
    next := s.next
    pc := (if evalICmp .ugt c ix = 1 then "land.lhs.true357.i" else "if.end372.i")
    pre := some s.pc }

/-- **`cond.end349.i`'s step.**  Class F's form: the bound's `phi`, the token marker's
`lifetime.start`, the position and gap stores, and the compare — and with
`execTerm_condbr_bit` the terminator is the two-arm jump the shapes state, so the
successor is named.

The `denote` is `walkCondEnd349_denote`'s, restored *at* `s` by `stateAt_self`: the
goal's `denoteCode` argument then stays the concrete block's, which is what lets the
step reduce at all. -/
theorem walkCondEnd349Step {sub : Calls} (s : State)
    {c ix : BitVec 64} {reg p : String} {tk gap : Nat}
    (hpc : s.pc = "cond.end349.i")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav : lookupName s.env reg = some (.int 64 c))
    (htok : lookupName s.env "%t352.i" = some (.ptr tk))
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (hgap : lookupName s.env "%gap.i" = some (.ptr gap)) :
    LeanLLVM.step (stage2Calls sub) stage2Body s =
      .jump (condEnd349OutAt s c ix tk gap) := by
  have hden : denoteCode (stage2Calls sub) walkCondEnd349.instrs s =
      some { condEnd349OutAt s c ix tk gap with pc := s.pc, pre := s.pre } := by
    have h := walkCondEnd349_denote (sub := sub) (env := s.env) (s := s) (c := c)
      (ix := ix) (tk := tk) (gap := gap) (reg := reg) (p := p)
      hpre hinc hav htok hidx hgap
    simpa only [stateAt_self, stateAt, condEnd349OutAt]
  have hfind : stage2Body.findBlock s.pc = some walkCondEnd349 := by
    rw [hpc]; exact walkCondEnd349_find
  have hterm : walkCondEnd349.term =
      Term.condbr (Operand.reg "%cmp355.i") "land.lhs.true357.i" "if.end372.i" := rfl
  simp only [LeanLLVM.step, hfind, hden, hterm]
  rw [execTerm_condbr_bit (bit := evalICmp .ugt c ix) _ (walkBitVec1_zero_or_one _)]
  · simp only [condEnd349OutAt]
  · simp only [evalOperand, condEnd349OutAt, cells, lookupName_cons_self]

/-- **A byte outside the run's whole touched extent is outside its frame.**  The
seed's version (`walkSeedWide_outside`) is stated at `walkSeed G S`, whose cursors are
the staging's; a chain's carries have advanced, so the bounds are the *carry's*
(`C.alen`, `C.evlen`) and the proof is the seed's with the cursor names substituted.

This is what a scan link's loaded-byte derivation runs on: `walkWide` never covers the
document, so a document byte reads as the caller's — `G.doc`'s own. -/
theorem walkWide_outside {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {a m : Nat}
    (hArena : a + m ≤ G.dst ∨ G.dst + C.alen ≤ a)
    (hEv : a + m ≤ G.ev ∨ G.ev + C.evlen ≤ a)
    (hSeven : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ a ∨ a + m ≤ r.1)
    (hD : C.stage.d + 8 ≤ a ∨ a + m ≤ C.stage.d)
    (hwm : a + m ≤ G.next0) {e : Nat} (ha : a ≤ e) (he : e < a + m) :
    ¬ inRegions (walkWide G C) e := by
  rintro ⟨r, hr, hlo, hhi⟩
  simp only [walkWide, walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr'
      · rcases hArena with h' | h' <;> omega
      · rcases List.mem_cons.mp hr' with rfl | hnil
        · rcases hEv with h' | h' <;> omega
        · exact absurd hnil (by simp)
    · rcases List.mem_append.mp hr with hr | hr
      · rcases hSeven r hr with h' | h' <;> omega
      · rcases List.mem_cons.mp hr with rfl | hnil
        · rcases hD with h' | h' <;> omega
        · exact absurd hnil (by simp)
  · exact not_walkAlloca_of_lt (by omega) ⟨r, hr, hlo, hhi⟩

/-- **The document's bytes are outside the run's frame, at any carry.**  The seed's
version (`walkSeed_doc_out`) is stated at `walkSeed G S`; a chain's carry has advanced,
so the arena and event comparisons are the *carry's* — but the document lies below both
(`stage2Regions`' first entry against the third and the fourth), so the two bounds are
those clauses read at the carry's cursors and not a search.

The carry's two bounds are the invariant's: `C.alen ≤ ndst0 + n + reserve` is
`alen_le` plus the reserve, and `C.evlen ≤ G.evcap` is `evlen_le` through `evRoom`. -/
theorem walkWide_doc_out {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    {e : Nat} (ha : G.b ≤ e) (he : e < G.b + G.n) :
    ¬ inRegions (walkWide G C) e := by
  have hsep := disjointRegions_staged_prefix C.stage.separate
  have h03 := stage2Regions_sep hsep (i := 0) (j := 3)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  have h04 := stage2Regions_sep hsep (i := 0) (j := 4)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  simp only [stage2Regions, List.getElem_cons_zero, List.getElem_cons_succ] at h03 h04
  have hnev : G.nev0 ≤ G.evcap := walkGeom_nev_le G
  refine walkWide_outside G C (a := G.b) (m := G.n) ?_ ?_ ?_ ?_ ?_ ha he
  · rcases h03 with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases h04 with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro r hr
    rcases stage2StagedWrites_against (a := G.b) (m := G.n + stage2ReadTail)
      C.stage.separate (by simp [stage2Regions]) r hr with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by omega)
  · rcases C.stage.dSep (G.b, G.n + stage2ReadTail)
      (by simp [stage2WalkRegions, stage2Regions]) with hd | hd
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · have hwm := G.watermark (G.b, G.n + stage2ReadTail) (by simp [stage2Regions])
    omega

/-- **A document byte reads as the caller's.**  The document is outside the run's
frame at every carry (`walkWide_doc_out`), so the byte a scan loads is `G.doc`'s own —
the derivation the accounting promised in place of a carry field: the invariant's frame
plus the geometry's document, and nothing about the scan. -/
theorem walkDoc_byte {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap) {q : Nat} (hq : q < G.n) :
    readBytes s.mem (G.b + q) 1 = some [G.bs.getD q 0] := by
  have hreads : readBytes s.mem (G.b + q) 1 = readBytes m0 (G.b + q) 1 :=
    readBytes_eq_of_UnchangedOn (unchangedOutside_iff_inRegions.mp hInv.frame)
      (fun k hk => walkWide_doc_out G C halen hevlen (by omega) (by omega))
  rw [hreads]
  exact walkReadBytes_one_of_readByte (readByte_of_readBytes G.doc hq)

/-! ### The trace's step shapes

`WalkLink` carries `step : step calls stage2Body s = .jump s'`, so a chain names every
state it passes through — but each class's *lemma* returns `∃ s', WalkLink … s'`, and
the witness it invents is not the state a chain must thread.  Composing a `WalkChain`
therefore needs each block's step at the state the invariant gives, with the target
named.  The two shapes below are the ones whose target depends on nothing the block's
instructions compute — an empty instruction list with a `br` (class B) and with a
`condbr` on a carried bit (class B′) — so their targets are the source state with the
edge's destination and predecessor, and the class's nine-plus-one instances are the
`find`/`term` pair of each block.

**The classes are not one shape each.**  Measured off the pinned body, class G's
fourteen blocks are six shapes — `load+load+binop+icmp` (`if.end.i.i`,
`if.end.i.i55`), `gep+load+icmp` (`lor.lhs.false.i`), `binop+zext+gep+load+icmp`
(`if.end179.i`, `land.lhs.true.i`), `gep+load+binop+icmp` (`if.then231.i`),
`gep+load+zext` (`cond.true345.i`), `gep+load` (`land.lhs.true357.i`) — beside two
long chains (`if.end59.i`, `if.end133.i`).  Class D divides the same way (`store`
alone, `gep+store`), and E is `phi`-headed, one shape per terminator.

So the count of shapes to write is the count of distinct opcode sequences, not the
count of classes — and the second measurement decides whether a repeated sequence
earns one.  A shape over *variable* names must take the intermediate cells as
hypotheses: with literal names `simp [lookupName]` peels a cons because the head
inequality is decidable at elaboration, while with parameters the same goal becomes
`dl₂ = dl₁ → nc = nl`, which the statement does not carry.  An instance discharges
each of those by `by simp [lookupName]` at its own literals, so **a shape's hypotheses
approach the instance's own proof**: it pays at two instances and is a loss below
that.  The rule, for every remaining block: repeated sequence → shape; once → instance.

**The rule's boundary.**  "Once → instance" holds only for a block whose sequence an
*existing* shape covers.  A block ending in a `br` cannot compute its own `step`
against the `def` of the block: `step`'s unfolding has already turned the block's
`instrs` and `term` into literals, so a `denoteCode` fact stated at `B.instrs` no
longer matches and the `match` does not reduce.  The block has to stay symbolic, and
that is what a shape is — so the single-block sequences that end in a `br` need a
shape too, and `walkGepLoadBrStep` is one: it serves `land.lhs.true357.i` directly and
`land.rhs.i` and `while.body370.i` after their `phi` runs, three blocks for one shape
under either reading.

**A call block's terminator is a step of its own.**  Class F's links never compute their
terminators: `WalkLink.pureCore` takes the term's `Ctrl` as a hypothesis, so the term is
the caller's to prove and the link's target stays existential.  A chain step must *name*
its successor, so the terminator has to be computed after all — and the only form in
which `execTerm`'s match reduces is the one whose `denote` is restored *at* the state the
step is stated at (`walkCondEnd349_denote` with `env := s.env`, then `stateAt_self`); a
`denote` stated through `stateAt s.env s` leaves the goal's `denoteCode` argument
different from the block's and the match stays under its catch-all.

Two of the shapes' statements are not free choices, and each cost a round to find.
A `phi`-headed block's target carries `pre := some (s.bindAll vs).pc`, not `some s.pc`:
`bindAll` extends the environment and its `pc` is not definitionally the source's, so
the `Ctrl.jump` equality the step closes by does not reduce.  And a `condbr` on a cell
the block's own instructions bound needs `evalOperand` in the simp set *before* the
cell's `lookupName` fact fires — the fact is about the environment, and `execTerm`
reaches it through `evalOperand`, so `simp only [hbit]` alone leaves the match
unreduced. -/

/-- **Class G's stack-marker variant: an index, a load and a compare.**  `if.end179.i`
and `land.lhs.true.i` are the same five instructions at their own names — the depth's
`add`, its `zext`, the stack's `gep`, the byte's `load` and the compare against one —
so the variant that repeats gets a step, and the four single-block sequences of the
class stay instances under the same rule.

The target is `walkMarkerEnv`, the named environment the class's links already state
their `WalkLocal` hypotheses at, so an instance's local facts need no transport.  The
`denoteCode` chain is the variant's own and is the one `WalkLink.stackMarkerBr`
carries; the difference is again only that the step names the successor. -/
theorem walkStackMarkerStep {calls : Calls} (s : State) {B : Block}
    {gg zx ap ld d base tl fl : String} {x c : BitVec 32} {a : Nat} {one : BitVec 8}
    {bs : List UInt8} {q : Nat}
    (hfind : stage2Body.findBlock s.pc = some B)
    (hinstrs : B.instrs = [
      Instr.binop gg BinOp.add 32 (.reg "%sp.i.0248") (.imm (.int 32 c)),
      Instr.zext zx 32 64 (.reg gg),
      Instr.gep ap (.int 8) (.reg base) (.reg zx),
      Instr.load ld (.int 8) (.reg ap),
      Instr.icmp d IPred.eq 8 (.reg ld) (.imm (.int 8 one))])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 x))
    (hbase : lookupName s.env base = some (.ptr a))
    (hzb : zx ≠ base) (hgb : gg ≠ base)
    (hpos : (x + c).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (x + c).toNat) 1 = some bs)
    (hbs : bytesToNat bs = q)
    (hbit : evalICmp .eq (BitVec.ofNat 8 q) one = 0 ∨
      evalICmp .eq (BitVec.ofNat 8 q) one = 1) :
    step calls stage2Body s =
      .jump { stateAt (walkMarkerEnv gg zx ap ld d x c a q one s.env) s with
        pc := (if evalICmp .eq (BitVec.ofNat 8 q) one = 1 then tl else fl)
        pre := some s.pc } := by
  have hden : denoteCode calls B.instrs s =
      some (stateAt (walkMarkerEnv gg zx ap ld d x c a q one s.env) s) := by
    rw [hinstrs, ← stateAt_self s]
    rw [walkDenoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := gg)
      (a := "%sp.i.0248") (w := 32) (x := x) (c := c) hsp]
    rw [denoteCode_zext (calls := calls) (env := (gg, .int 32 (x + c)) :: s.env) (s := s)
      (d := zx) (v := gg) (wIn := 32) (wOut := 64) (x := x + c) (by simp [lookupName])]
    rw [denoteCode_gep8_ofNat (calls := calls)
      (env := (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ap) (base := base) (off := zx) (a := a) (j := (x + c).toNat)
      (by rw [lookupName_cons_ne (k := zx) (n := base) _ _ hzb,
              lookupName_cons_ne (k := gg) (n := base) _ _ hgb]; exact hbase)
      (by simp [lookupName]) hpos]
    rw [denoteCode_load8 (calls := calls)
      (env := (ap, .ptr (a + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ld) (p := ap) (a := a + (x + c).toNat) (q := q) (bs := bs)
      (by simp [lookupName]) hread hbs]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := (ld, .int 8 (BitVec.ofNat 8 q)) :: (ap, .ptr (a + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := d) (a := ld) (w := 8) (x := BitVec.ofNat 8 q) (c := one)
      (by simp [lookupName])]
    rfl
  simp only [step, hfind, hden, hterm, execTerm]
  simp only [evalOperand, stateAt, walkMarkerEnv, cells, lookupName_cons_self]
  rcases hbit with h | h <;> simp [h]

/-- **Class G's tag-reserve shape: two loads, an add, a compare.**  `if.end.i.i` and
`if.end.i.i55` are the same four instructions at their own names — the log's length
and capacity words, the length's increment, and the test that the increment does not
pass the capacity — so the class's repeated variant is one step.  The target is the
four cells the chain binds and the arm the comparison picks, at
`stateAt (cells …)` for the same reason `walkAddIcmpBrStep` states it there: the
class's links take their `WalkLocal` hypotheses at that form. -/
theorem walkTwoLoadAddIcmpStep {calls : Calls} (s : State) {b : Block}
    {dl₁ dl₂ dadd dcmp pl₁ pl₂ tl fl : String} {al ac : Nat} {nl nc : BitVec 64}
    (hfind : stage2Body.findBlock s.pc = some b)
    (his : b.instrs = [
      Instr.load dl₁ (Ty.int 64) (.reg pl₁),
      Instr.load dl₂ (Ty.int 64) (.reg pl₂),
      Instr.binop dadd BinOp.add 64 (.reg dl₁)
        (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp dcmp IPred.ugt 64 (.reg dadd) (.reg dl₂)])
    (ht : b.term = Term.condbr (.reg dcmp) tl fl)
    (h₁ : lookupName s.env pl₁ = some (.ptr al))
    (h₂ : lookupName ((dl₁, .int 64 nl) :: s.env) pl₂ = some (.ptr ac))
    (hr₁ : readBytes s.mem al 8 = some (natToBytes nl.toNat 8))
    (hr₂ : readBytes s.mem ac 8 = some (natToBytes nc.toNat 8))
    (hadd : lookupName ((dl₂, .int 64 nc) :: (dl₁, .int 64 nl) :: s.env) dl₁ =
      some (.int 64 nl))
    (hic₁ : lookupName ((dadd, .int 64 (nl + BitVec.ofNat 64 1)) ::
      (dl₂, .int 64 nc) :: (dl₁, .int 64 nl) :: s.env) dadd =
      some (.int 64 (nl + BitVec.ofNat 64 1)))
    (hic₂ : lookupName ((dadd, .int 64 (nl + BitVec.ofNat 64 1)) ::
      (dl₂, .int 64 nc) :: (dl₁, .int 64 nl) :: s.env) dl₂ = some (.int 64 nc))
    (hbit : evalICmp .ugt (nl + BitVec.ofNat 64 1) nc = 0 ∨
      evalICmp .ugt (nl + BitVec.ofNat 64 1) nc = 1) :
    step calls stage2Body s =
      .jump { stateAt (cells
          [(dcmp, .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)),
           (dadd, .int 64 (nl + BitVec.ofNat 64 1)),
           (dl₂, .int 64 nc),
           (dl₁, .int 64 nl)] s.env) s with
        pc := (if evalICmp .ugt (nl + BitVec.ofNat 64 1) nc = 1 then tl else fl)
        pre := some s.pc } := by
  have hden : denoteCode calls b.instrs s =
      some (stateAt (cells
        [(dcmp, .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)),
         (dadd, .int 64 (nl + BitVec.ofNat 64 1)),
         (dl₂, .int 64 nc),
         (dl₁, .int 64 nl)] s.env) s) := by
    rw [his]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load64 (calls := calls) (env := s.env) (s := s) (d := dl₁)
      (p := pl₁) (a := al) (v := nl) h₁ hr₁]
    rw [denoteCode_load64 (calls := calls) (env := (dl₁, .int 64 nl) :: s.env)
      (s := s) (d := dl₂) (p := pl₂) (a := ac) (v := nc) h₂ hr₂]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := (dl₂, .int 64 nc) :: (dl₁, .int 64 nl) :: s.env) (s := s)
      (d := dadd) (a := dl₁) (w := 64) (x := nl) (c := BitVec.ofNat 64 1) hadd]
    rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_reg_w (calls := calls)
      (env := (dadd, .int 64 (nl + BitVec.ofNat 64 1)) ::
        (dl₂, .int 64 nc) :: (dl₁, .int 64 nl) :: s.env) (s := s)
      (d := dcmp) (a := dadd) (b := dl₂) IPred.ugt 64
      (x := nl + BitVec.ofNat 64 1) (y := nc)
      hic₁ hic₂]
    rfl
  simp only [step, hfind, hden, ht, execTerm]
  simp only [evalOperand, stateAt, cells, lookupName_cons_self]
  rcases hbit with h | h <;> simp [h]

/-- **Class H1: the arithmetic latch.**  `add` an immediate into a fresh name, compare
it against a bound, branch on the bit — ten blocks, the dispatch's range tests.  The
target is the two cells the pair binds and the arm the comparison picks, stated at
`stateAt (cells …)` because that is the form the class's links take their `WalkLocal`
hypotheses at, so an instance's local facts line up without a transport. -/
theorem walkAddIcmpBrStep {calls : Calls} (s : State) {b : Block} {reg off d : String}
    {c one : BitVec 8} {tl fl : String} {x : BitVec 8}
    (hfind : stage2Body.findBlock s.pc = some b)
    (hinstrs : b.instrs = [Instr.binop off BinOp.add 8 (.reg reg) (.imm (.int 8 c)),
      Instr.icmp d IPred.ule 8 (.reg off) (.imm (.int 8 one))])
    (hterm : b.term = Term.condbr (.reg d) tl fl)
    (hreg : lookupName s.env reg = some (.int 8 x))
    (hbit : evalICmp .ule (x + c) one = 0 ∨ evalICmp .ule (x + c) one = 1) :
    step calls stage2Body s =
      .jump { stateAt (cells [(d, .int 1 (evalICmp .ule (x + c) one)),
          (off, .int 8 (x + c))] s.env) s with
        pc := (if evalICmp .ule (x + c) one = 1 then tl else fl)
        pre := some s.pc } := by
  have hden : denoteCode calls b.instrs s =
      some (stateAt (cells [(d, .int 1 (evalICmp .ule (x + c) one)),
        (off, .int 8 (x + c))] s.env) s) := by
    rw [hinstrs, ← stateAt_self s,
      walkDenoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := off)
        (a := reg) (w := 8) (x := x) (c := c) hreg]
    rw [walkDenoteCode_icmp (calls := calls) (env := (off, .int 8 (x + c)) :: s.env)
      (s := s) d 8 IPred.ule (x := x + c) (y := one)
      (by simp only [stateAt, evalOperand, lookupName_cons_self])
      (by exact evalOperand_lit_of _ _ _) []]
    rfl
  simp only [step, hfind, hden, hterm, execTerm]
  simp only [evalOperand, stateAt, cells, lookupName_cons_self]
  rcases hbit with h | h <;> simp [h]

/-- **Class E: a `phi` run and a branch.**  The class's fifteen blocks all open with a
`phi` run, which `denoteCode` takes in one step: the selection is by predecessor
(`PhiSelects`), and what follows runs at the environment the selected cells extend.
Stated this way the class needs one shape per terminator rather than one per block,
and a block's instance is its `phi` list, its predecessor and its edge.

That is the *pure* form, and the class is not all of that form: a block that runs work
after its `phi`s needs the run composed with the class that work belongs to
(`land.rhs.i`, `while.body370.i` and `if.end245.i` are `phi` + `gep` + `load` + `br`).
So nothing new is owed — `denoteCode_phiRun` is already the general statement, the
selection and then the rest at the selected environment — and what such a block's
instance costs is two rewrites rather than one: the run's, then its body's shape.

The target is `s.bindAll vs` — the selection's cells — at the edge's destination, so
an instance's facts are `PhiSelects`' own and nothing about the block's name. -/
theorem walkPhiBrStep {calls : Calls} (s : State) {B : Block} {specs : List PhiSpec}
    {vs : List (String × Value)} {p dest : String}
    (hfind : stage2Body.findBlock s.pc = some B)
    (hinstrs : B.instrs = specs.map PhiSpec.instr)
    (hterm : B.term = Term.br dest)
    (hpre : s.pre = some p)
    (hsel : PhiSelects s p specs vs) :
    step calls stage2Body s =
      .jump { s.bindAll vs with pc := dest, pre := some (s.bindAll vs).pc } := by
  have hden : denoteCode calls B.instrs s = some (s.bindAll vs) := by
    rw [hinstrs]
    have h := denoteCode_phiRun (calls := calls) (s := s) (p := p) (specs := specs)
      (vs := vs) (rest := []) hpre hsel (by rfl)
    simpa only [List.append_nil, denoteCode_nil] using h
  simp only [step, hfind, hden, hterm, execTerm]

/-- **Class E, the branching terminator.**  The block's `phi` run, then a `condbr` on
a cell the run bound — the selection's own register, so the bit is a lookup at the
extended environment and the arm is the one `evalICmp`-shaped facts already name. -/
theorem walkPhiCondbrStep {calls : Calls} (s : State) {B : Block}
    {specs : List PhiSpec} {vs : List (String × Value)} {p d tl fl : String}
    {bit : BitVec 1}
    (hfind : stage2Body.findBlock s.pc = some B)
    (hinstrs : B.instrs = specs.map PhiSpec.instr)
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (hpre : s.pre = some p)
    (hsel : PhiSelects s p specs vs)
    (hbit : lookupName (s.bindAll vs).env d = some (.int 1 bit))
    (hb01 : bit = 0 ∨ bit = 1) :
    step calls stage2Body s =
      .jump { s.bindAll vs with
        pc := (if bit = 1 then tl else fl), pre := some (s.bindAll vs).pc } := by
  have hden : denoteCode calls B.instrs s = some (s.bindAll vs) := by
    rw [hinstrs]
    have h := denoteCode_phiRun (calls := calls) (s := s) (p := p) (specs := specs)
      (vs := vs) (rest := []) hpre hsel (by rfl)
    simpa only [List.append_nil, denoteCode_nil] using h
  simp only [step, hfind, hden, hterm, execTerm, evalOperand, hbit]
  rcases hb01 with rfl | rfl <;> simp

/-- **The `gep`-and-load shape: a register-indexed address and the byte it holds.**
Three of the walk's blocks end this way — `land.lhs.true357.i` on its own, and
`land.rhs.i` and `while.body370.i` after their `phi` runs — so the sequence is a shape
and not an instance, and the two `phi`-headed ones compose it with
`denoteCode_phiRun`.

It is also the case that settles the cost rule's boundary: an instance whose block
ends in a `br` cannot compute its own `step` against the *def* of the block, because
`step`'s unfolding has already turned the block's `instrs` and `term` into literals
and the `denoteCode` fact no longer matches.  The block must stay symbolic, which is
what a shape is — so "once → instance" holds only for a block whose sequence an
*existing* shape covers. -/
theorem walkGepLoadBrStep {calls : Calls} (s : State) {B : Block}
    {ap ld base off dest : String} {a j : Nat} {b : UInt8}
    (hfind : stage2Body.findBlock s.pc = some B)
    (hinstrs : B.instrs = [Instr.gep ap (Ty.int 8) (.reg base) (.reg off),
      Instr.load ld (.int 8) (.reg ap)])
    (hterm : B.term = Term.br dest)
    (hbase : lookupName s.env base = some (.ptr a))
    (hoff : lookupName s.env off = some (.int 64 (BitVec.ofNat 64 j)))
    (hj63 : j < 2 ^ 63)
    (hread : readBytes s.mem (a + j) 1 = some [b]) :
    LeanLLVM.step calls stage2Body s =
      .jump { stateAt (cells [(ld, .int 8 (BitVec.ofNat 8 b.toNat)),
          (ap, .ptr (a + j))] s.env) s with
        pc := dest, pre := some s.pc } := by
  have hden : denoteCode calls B.instrs s =
      some (stateAt (cells [(ld, .int 8 (BitVec.ofNat 8 b.toNat)),
        (ap, .ptr (a + j))] s.env) s) := by
    rw [hinstrs, ← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s) (d := ap)
      (base := base) (off := off) (a := a) (idx := BitVec.ofNat 64 j)
      hbase hoff (by rw [sExt_ofNat64 hj63]; exact hj63)]
    rw [sExt_ofNat64 hj63]
    rw [denoteCode_load8_single (calls := calls)
      (env := (ap, .ptr (a + j)) :: s.env) (s := s)
      (d := ld) (p := ap) (a := a + j) (by simp [lookupName]) hread]
    rfl
  simp only [LeanLLVM.step, hfind, hden, hterm, execTerm]
  rfl

/-- **A `phi` run and the `gep`-and-load body.**  `land.rhs.i` and `while.body370.i`
are the same block: the counter's `phi`, the register-indexed address, the byte it
loads, and a `br` — so the E-bodied form is a shape, and the run composes with
`walkGepLoadBrStep`'s sequence at the selected environment.  The target is stated at
`s.bindAll vs`, the environment the selection leaves, so an instance's local facts are
`PhiSelects`' own. -/
theorem walkPhiGepLoadBrStep {calls : Calls} (s : State) {B : Block}
    {specs : List PhiSpec} {vs : List (String × Value)} {p : String}
    {ap ld base off dest : String} {a j : Nat} {b : UInt8}
    (hfind : stage2Body.findBlock s.pc = some B)
    (hinstrs : B.instrs = specs.map PhiSpec.instr ++
      [Instr.gep ap (Ty.int 8) (.reg base) (.reg off),
       Instr.load ld (.int 8) (.reg ap)])
    (hterm : B.term = Term.br dest)
    (hpre : s.pre = some p)
    (hsel : PhiSelects s p specs vs)
    (hbase : lookupName (s.bindAll vs).env base = some (.ptr a))
    (hoff : lookupName (s.bindAll vs).env off = some (.int 64 (BitVec.ofNat 64 j)))
    (hj63 : j < 2 ^ 63)
    (hread : readBytes (s.bindAll vs).mem (a + j) 1 = some [b]) :
    LeanLLVM.step calls stage2Body s =
      .jump { stateAt (cells [(ld, .int 8 (BitVec.ofNat 8 b.toNat)),
          (ap, .ptr (a + j))] (s.bindAll vs).env) (s.bindAll vs) with
        pc := dest, pre := some (s.bindAll vs).pc } := by
  have hbody : denoteCode calls
      [Instr.gep ap (Ty.int 8) (.reg base) (.reg off),
       Instr.load ld (.int 8) (.reg ap)] (s.bindAll vs) =
      some (stateAt (cells [(ld, .int 8 (BitVec.ofNat 8 b.toNat)),
        (ap, .ptr (a + j))] (s.bindAll vs).env) (s.bindAll vs)) := by
    rw [← stateAt_self (s.bindAll vs)]
    rw [denoteCode_gep8_reg (calls := calls) (env := (s.bindAll vs).env)
      (s := s.bindAll vs) (d := ap) (base := base) (off := off) (a := a)
      (idx := BitVec.ofNat 64 j) hbase hoff (by rw [sExt_ofNat64 hj63]; exact hj63)]
    rw [sExt_ofNat64 hj63]
    rw [denoteCode_load8_single (calls := calls)
      (env := (ap, .ptr (a + j)) :: (s.bindAll vs).env) (s := s.bindAll vs)
      (d := ld) (p := ap) (a := a + j) (by simp [lookupName]) hread]
    rfl
  have hden : denoteCode calls B.instrs s =
      some (stateAt (cells [(ld, .int 8 (BitVec.ofNat 8 b.toNat)),
        (ap, .ptr (a + j))] (s.bindAll vs).env) (s.bindAll vs)) := by
    rw [hinstrs]
    rw [denoteCode_phiRun (specs := specs) (vs := vs)
      (rest := [Instr.gep ap (Ty.int 8) (.reg base) (.reg off),
        Instr.load ld (.int 8) (.reg ap)]) hpre hsel (by rfl)]
    exact hbody
  simp only [LeanLLVM.step, hfind, hden, hterm, execTerm]
  rfl

/-- **Class A: one comparison and a branch.**  Sixty of the walk's blocks are this
shape — one `icmp` into a fresh name and a `condbr` on it — which makes the class a
single step: the target's environment carries the comparison's cell and its `pc` is
the bit's arm, so a block's instance is the pair `find`/`term` and its two operands'
values.

The bit is a hypothesis rather than a fact of the terminator, and that is what lets
a chain's case split be the one it already carries: `execTerm`'s `condbr` has two
arms and an `ub` for a bit that is neither, while an `icmp`'s value is always one of
the two, so the disjunction is discharged at the instantiation. -/
theorem walkIcmpBrStep {calls : Calls} (s : State) {b : Block} {d : String}
    {pred : IPred} {w : Nat} {a₁ a₂ : Operand} {t f : String} {x y : BitVec w}
    (hfind : stage2Body.findBlock s.pc = some b)
    (his : b.instrs = [Instr.icmp d pred w a₁ a₂])
    (ht : b.term = Term.condbr (.reg d) t f)
    (hx : evalOperand s a₁ = some (.int w x))
    (hy : evalOperand s a₂ = some (.int w y))
    (hbit : evalICmp pred x y = 0 ∨ evalICmp pred x y = 1) :
    step calls stage2Body s =
      .jump { (s.bind d (.int 1 (evalICmp pred x y))) with
        pc := (if evalICmp pred x y = 1 then t else f)
        pre := some s.pc } := by
  have hden : denoteCode calls b.instrs s =
      some (s.bind d (.int 1 (evalICmp pred x y))) := by
    rw [his]
    rw [denoteCode_cons_of calls (Instr.icmp d pred w a₁ a₂) [] s
      (s.bind d (.int 1 (evalICmp pred x y)))
      (LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp hx hy)]
    simp only [denoteCode_nil]
  simp only [step, hfind, hden, ht, execTerm]
  dsimp only [State.bind]
  simp only [evalOperand, lookupName_cons_self]
  rcases hbit with h | h <;> simp [h]

/-! ### Class A's instances

Each block's link lemma returns `∃ s', WalkLink … s'`; the step shape names the
target.  Both compute the same `step` from the same two operand facts, so
`Ctrl.jump`'s injectivity identifies the link's witness with the named state — the
pattern `walkBack_step_at` uses at the merge.  An instance is therefore its block's
`find`/`term`, its operand's value, and the two rewrites; nothing about the block's
name enters the proof.

The first instance proves the pattern.  The other fifty-nine are the same text with
the block's own comparison and edges, which is what the class's proof obligation is
once the shape is stated. -/

/-- **`LeafBlock99`'s target, named.**  The link's witness is the state
`walkIcmpBrStep` names: the comparison's cell, and the arm its bit picks. -/
theorem WalkLink.LeafBlock99_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock99")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body462.i" }
      { stateAt (("%SwitchLeaf100", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with
        pc := "while.body462.i", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1
            then "while.body462.i" else "if.then467.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf100"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1
          then "while.body462.i" else "if.then467.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock99 G C s hInv hblock h1 hl
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock99) (d := "%SwitchLeaf100") (pred := IPred.eq) (w := 8)
    (a₁ := .reg "%47") (a₂ := .imm (.int 8 (BitVec.ofNat 8 13)))
    (t := "while.body462.i") (f := "if.then467.i")
    (x := x1) (y := BitVec.ofNat 8 13)
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock99_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **Class B: an empty block and a `br`.**  The target is the source with the edge's
destination; nothing the block does moves a register or a byte. -/
theorem walkBrStep {calls : Calls} (s : State) {b : Block} {dest : String}
    (hfind : stage2Body.findBlock s.pc = some b)
    (his : b.instrs = []) (ht : b.term = Term.br dest) :
    step calls stage2Body s = .jump { s with pc := dest, pre := some s.pc } := by
  simp only [step, hfind, his, denoteCode_nil, ht, execTerm]

/-- **Class B′: an empty block and a `condbr` on a carried bit.**  The target's `pc`
is the bit's arm, unfolded so the caller's case split on the bit is the one the step
takes. -/
theorem walkCondbrStep {calls : Calls} (s : State) {b : Block} {c : Operand}
    {t f : String} {bit : BitVec 1}
    (hfind : stage2Body.findBlock s.pc = some b)
    (his : b.instrs = []) (ht : b.term = Term.condbr c t f)
    (hv : evalOperand s c = some (.int 1 bit))
    (hbit : bit = 0 ∨ bit = 1) :
    step calls stage2Body s =
      .jump { s with pc := (if bit = 1 then t else f), pre := some s.pc } := by
  simp only [step, hfind, his, denoteCode_nil, ht, execTerm, hv]
  rcases hbit with rfl | rfl <;> simp

/-! ### The exit's tail blocks

Three of the tail's blocks are steps rather than links, because what the exit owes
is a run to the return and not a measure's non-increase.  `if.then485.i` is the
depth's zero test — the dispatch's `icmp .eq i32 %sp.i.1, 0`, whose bit names
`if.end490.i` or `if.then488.i`; `if.end490.i` is the root-done flag's last test,
a load of `%root_done.i` and the `icmp .eq i32` of its four bytes against zero. -/

/-- **`if.then485.i`'s step.**  The depth's zero test, at the register the merge
left: the bit is `%sp.i.1 == 0`, and the terminator takes `if.end490.i` on it and
`if.then488.i` off it. -/
theorem walkIfThen485Step {calls : Calls} (s : State) (hpc : s.pc = "if.then485.i")
    {spv : Nat}
    (hsp : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv))) :
    step calls stage2Body s =
      .jump { (s.bind "%48"
          (.int 1 (evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0)))) with
        pc := (if evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
          then "if.end490.i" else "if.then488.i")
        pre := some s.pc } := by
  have hden : denoteCode calls walkIf_then485_i.instrs s =
      some (s.bind "%48"
        (.int 1 (evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0)))) := by
    simp only [walkIf_then485_i]
    rw [← stateAt_self s]
    rw [denoteCode_icmp_eq_imm_w (calls := calls) (env := s.env) (s := s)
      (d := "%48") (a := "%sp.i.1") (w := 32) (x := BitVec.ofNat 32 spv)
      (c := BitVec.ofNat 32 0) (by simpa [lookupName] using hsp)]
    rfl
  have hterm : walkIf_then485_i.term =
      Term.condbr (Operand.reg "%48") "if.end490.i" "if.then488.i" := rfl
  simp only [step, hpc, walkIf_then485_i_find, hden, hterm]
  dsimp only [State.bind]
  simp only [execTerm, evalOperand, lookupName_cons_self, hpc]
  rcases walkBitVec1_zero_or_one (evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0))
    with h | h <;> simp [h]

/-- **`if.end490.i`'s step.**  The root-done flag's last test: the four bytes at
`%root_done.i` are `%.pr`, and its zero test is the bit that takes
`if.then492.i` — the refusal copy — or `s2_walk.exit`. -/
theorem walkIfEnd490Step {calls : Calls} (s : State) (hpc : s.pc = "if.end490.i")
    {rd : Nat} {v : BitVec 32}
    (hroot : lookupName s.env "%root_done.i" = some (.ptr rd))
    (hread : readBytes s.mem rd 4 = some (natToBytes v.toNat 4)) :
    step calls stage2Body s =
      .jump { ((s.bind "%.pr" (.int 32 v)).bind "%tobool491.not.i"
          (.int 1 (evalICmp .eq v (BitVec.ofNat 32 0)))) with
        pc := (if evalICmp .eq v (BitVec.ofNat 32 0) = 1 then "if.then492.i"
          else "s2_walk.exit")
        pre := some s.pc } := by
  have hden : denoteCode calls walkIf_end490_i.instrs s =
      some ((s.bind "%.pr" (.int 32 v)).bind "%tobool491.not.i"
        (.int 1 (evalICmp .eq v (BitVec.ofNat 32 0)))) := by
    simp only [walkIf_end490_i]
    conv_lhs => rw [← stateAt_self s]
    rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_load_i32 (calls := calls)
      (env := s.env) (s := s)
      (d := "%.pr") (p := "%root_done.i") (a := rd) (v := v) hroot hread]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%.pr", .int 32 v) :: s.env) (s := s)
      (d := "%tobool491.not.i") (a := "%.pr") (w := 32) (x := v)
      (c := BitVec.ofNat 32 0) (by simp [lookupName])]
    rfl
  have hterm : walkIf_end490_i.term =
      Term.condbr (Operand.reg "%tobool491.not.i") "if.then492.i" "s2_walk.exit" := rfl
  simp only [step, hpc, walkIf_end490_i_find, hden, hterm]
  dsimp only [State.bind]
  simp only [execTerm, evalOperand, lookupName_cons_self, hpc]
  rcases walkBitVec1_zero_or_one (evalICmp .eq v (BitVec.ofNat 32 0)) with h | h <;> simp [h]

/-! ### The two refusal arms

`if.then488.i` and `if.then492.i` are one instruction pair each — `%off = %e + 8`
and the store of `%4` there — and both branch to `if.then`, the refusal copy.  They
are the two entries into the exit's refusal arm: the depth's non-zero test goes
straight to the first, and the root-done flag's zero test to the second.  What they
write is the refusal offset, the number the wrapper's `if.then` then copies into the
record's slot, so the step names the state it leaves rather than only its edge. -/

/-- **`if.then488.i`'s step.**  The depth's non-zero arm: `%off` is `%e + 8` and
`%4`'s word is stored there, then the branch to the refusal copy. -/
theorem walkIfThen488Step {calls : Calls} (s : State) (hpc : s.pc = "if.then488.i")
    {e : Nat} {v : Nat}
    (he : lookupName s.env "%e" = some (.ptr e))
    (h4 : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64) :
    step calls stage2Body s =
      .jump { { s with
          env := ("%off1.i.i115", .ptr (e + 8)) :: s.env
          mem := writeBytes s.mem (e + 8) (wordBytes 8 v) } with
        pc := "if.then", pre := some s.pc } := by
  have hden : denoteCode calls walkIf_then488_i.instrs s =
      some { s with
        env := ("%off1.i.i115", .ptr (e + 8)) :: s.env
        mem := writeBytes s.mem (e + 8) (wordBytes 8 v) } := by
    simp only [walkIf_then488_i]
    conv_lhs => rw [← stateAt_self s]
    rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_gep8_lit_w (calls := calls)
      (env := s.env) (s := s) (d := "%off1.i.i115") (base := "%e") (a := e)
      (w := 64) (n := BitVec.ofNat 64 8) (by simpa [lookupName] using he) (by decide)]
    simp only [show (BitVec.ofNat 64 8).signExtend 64 = BitVec.ofNat 64 8 from by decide,
      show (BitVec.ofNat 64 8).toNat = 8 from by decide]
    rw [denoteCode_store64_ofNat (calls := calls)
      (env := ("%off1.i.i115", .ptr (e + 8)) :: s.env) (s := s)
      (v := "%4") (p := "%off1.i.i115") (a := e + 8) (j := v)
      (by simpa [lookupName] using h4) hv64 (by simp [lookupName]) []]
    rfl
  have hterm : walkIf_then488_i.term = Term.br "if.then" := rfl
  simp only [step, hpc, walkIf_then488_i_find, hden, hterm]
  simp only [execTerm]

/-- **`if.then492.i`'s step.**  The root-done flag's zero arm: the same pair, at
its own `%off` name, then the refusal copy. -/
theorem walkIfThen492Step {calls : Calls} (s : State) (hpc : s.pc = "if.then492.i")
    {e : Nat} {v : Nat}
    (he : lookupName s.env "%e" = some (.ptr e))
    (h4 : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64) :
    step calls stage2Body s =
      .jump { { s with
          env := ("%off1.i.i117", .ptr (e + 8)) :: s.env
          mem := writeBytes s.mem (e + 8) (wordBytes 8 v) } with
        pc := "if.then", pre := some s.pc } := by
  have hden : denoteCode calls walkIf_then492_i.instrs s =
      some { s with
        env := ("%off1.i.i117", .ptr (e + 8)) :: s.env
        mem := writeBytes s.mem (e + 8) (wordBytes 8 v) } := by
    simp only [walkIf_then492_i]
    conv_lhs => rw [← stateAt_self s]
    rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_gep8_lit_w (calls := calls)
      (env := s.env) (s := s) (d := "%off1.i.i117") (base := "%e") (a := e)
      (w := 64) (n := BitVec.ofNat 64 8) (by simpa [lookupName] using he) (by decide)]
    simp only [show (BitVec.ofNat 64 8).signExtend 64 = BitVec.ofNat 64 8 from by decide,
      show (BitVec.ofNat 64 8).toNat = 8 from by decide]
    rw [denoteCode_store64_ofNat (calls := calls)
      (env := ("%off1.i.i117", .ptr (e + 8)) :: s.env) (s := s)
      (v := "%4") (p := "%off1.i.i117") (a := e + 8) (j := v)
      (by simpa [lookupName] using h4) hv64 (by simp [lookupName]) []]
    rfl
  have hterm : walkIf_then492_i.term = Term.br "if.then" := rfl
  simp only [step, hpc, walkIf_then492_i_find, hden, hterm]
  simp only [execTerm]

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
two blocks in it.

The dispatch's interior is not one path.  Five of its blocks open scans — the
whitespace skip, the two string scans, the escape list's and the number's — whose
visits are the entry's own bytes, so the revolution's trace is a finite path from
the head to the scans' latches, one induction per scan over its counter, and the
token's post-scan blocks to the merge.  `WalkSegment.trans` composes those pieces and
`WalkChain.append` composes the finite ones; what an induction supplies is a segment
whose `j` is the counter's own bound, which is why the price is stated per byte
(`stage2ByteAllowance`) rather than per block.  The byte term is what pays the scans: an entry's dispatch runs
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
seed's three steps and the two terminal ones (`walkExitFits`).

The run is stated in two pieces and its merge is named, because the post reads it
there: `Cend`/`sEnd` are the carry and state the last dispatch leaves at
`cleanup478.i`, the tail runs from `sEnd`, and the arena word at `sEnd` is
`Cend.alen` — the equality the exit's slot copy needs, and the lag inside an
iteration closed at the loop head.  `WalkInv.log_len` already gives the event
cursor's word as an equality, so the two slot copies are the same fact on the two
sides and only the arena's needs stating.

What the post owes beyond this premise is *not* a `writeBytes` identity.
Disjointness does not make two writes commute as memories: `writeByte` replaces a
present cell in place but appends an absent one, so a difference in order survives
as a difference in the list — `writeBytes_absent_comm_witness` is the two-write
counterexample (`JsonStage2StringBody`).  The order facts that do hold are the
pointwise one (a read outside both regions is unchanged) and the present one (a
write of the bytes already there is the identity), and the post needs neither in
its commuting form: every clause of `stage2Boundary` is a *read* at a named address
or a region claim, so the boundary can be proved at `sret.mem` directly — the two
copied words are `Cend.alen` (this premise) and `Cend.evlen` (`WalkInv.log_len`),
and the refusal offset is existential there (`∃ e, e ≤ n ∧ …`), so the memory's own
word serves rather than the carry's `eoff`. -/
def WalkExit (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (v : Value) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 = G.nep →
    ∃ (Cend : WalkCarry G) (sEnd : State), WalkInv G Cend sEnd ∧
      Cend.block = "cleanup478.i" ∧ Cend.k = G.nep ∧
      -- **The arena word is the cursor at the merge.**  The carry advances with
      -- each append (`arenaAppend`'s `alen' = alen + on`) and the block that
      -- writes `%z + 48` stores the same decoded length, so the lag
      -- `WalkInv.log_alen` allows is closed at the loop head.  The exit's slot
      -- copy reads this word, which is what identifies the run's final memory
      -- with the record's report.
      readBytes sEnd.mem (Cend.stage.z + 48) 8 = some (wordBytes 8 Cend.alen) ∧
      ∃ (q₁ q₂ : Nat) (s1 s2 sret : State),
        (∀ n, runFuel calls (q₁ + n) stage2Body s = runFuel calls n stage2Body sEnd) ∧
        q₁ + q₂ ≤ walkPotential G C + 27 ∧
        (∀ n, runFuel calls (q₂ + n) stage2Body sEnd = runFuel calls n stage2Body s1) ∧
        step calls stage2Body s1 = .jump s2 ∧
        step calls stage2Body s2 = .ret v sret

/-- **The empty entry stream's flush arm.**  The entry's own step and the refusal
copy reach a return, inside the finalisation allowance, whenever the entry count
is zero.

The empty stream is the all-whitespace document: a real input the reference
*refuses* and the record admits, so it is a branch of the completion rather than a
clause on the precondition.  The count is the entry state's own `%nep` — the ABI's
fourth argument, and nothing the entry block computes — so the premise reads it
from the state instead of taking it as a number; `nep = 0` selects the entry's
`if.then492.i` arm (`walkEntry_step`'s zero branch, `walkEntryJump`), whose store
and `if.then`'s copy are the refusal arm's (`walkIfThenBlock_denote`), and
`if.end` returns the refusal bit (`walkIfEnd_step`'s `0` arm).

The allowance is `stage2FinalisationAllowance`, which is the term `stage2Budget`
carries whatever the counts are: one step for the entry, one for the flush block,
one for the copy and one for the return, so the budget covers the arm at `nep = 0`
and at every document length.

The state is the record's own: the entry state at the ABI's thirteen words and the
eight the flattening appends, at a memory and a cursor.  Stating it at an arbitrary
state would be false — the entry block reads `%s`, `%z`, `%e`, the counts and the
appended pointers, so a state that is not an entry state at an argument list has no
run at all — which is why the premise is the completion *at the argument list*, and
the branch that uses it supplies the count's zero and the budget's allowance. -/
def WalkFlush (calls : Calls) (v0 : Value) (a13 : List Value) (nep : Nat)
    (d c ctype cst tok s z e : Nat) : Prop :=
  nep = 0 →
    ∀ (mem : Mem) (next : Nat),
      ∃ (q : Nat) (m : Mem), q ≤ stage2FinalisationAllowance ∧
        runFuel calls q stage2Body
          (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
          some (.ret v0 m)

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
  · obtain ⟨Cend, sEnd, -, -, -, -, q₁, q₂, s1, s2, sret, hseg1, hq, hseg2,
      hstep1, hret⟩ := hexit C s hInv hhead (by omega)
    refine Or.inr ⟨q₁ + q₂, s1, s2, sret, ?_, ?_, hstep1, hret⟩
    · omega
    · exact runFuel_prefix_trans hseg1 hseg2

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
at the value the exit returns (`WalkDispatch` beside `WalkExit`).

The seed conjunct is stated at `stage2Calls sub`, and the entry block's `s2_init`
call is the one place the selection enters it, and the premise names the selection
the pipeline uses: `stage2Calls stage2SubCalls`, which is what
`JsonStage2WalkSeedAtEntry`'s `walkSeedPrefix_entry_geometry` is proved at and what
`Stage2WalkObligation` states.  At any other selection the completion is false
rather than merely unproved — a selection may leave `s2_init` unanswered — so the
premise does not quantify over one. -/
def WalkPremises (d c ctype cst tok s z e nkSlot nxpSlot : Nat) : Prop :=
  ∀ (a13 : List Value) (mem : Mem) (next : Nat),
    Γ_stage2.pre a13 mem next →
    stage2StagedPre a13 mem next d c ctype cst tok s z e nkSlot nxpSlot →
    ∃ (m0 : Mem) (G : WalkGeom m0) (S : WalkStage G),
      G.next0 = next ∧
      a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] ∧
      ((G.nep = 0 ∧
          ∃ v0 : Value,
            WalkFlush (stage2Calls stage2SubCalls) v0 a13 G.nep d c ctype cst tok s z e) ∨
        (0 < G.nep ∧
        (∀ n, runFuel (stage2Calls stage2SubCalls) (3 + n) stage2Body
            (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
          runFuel (stage2Calls stage2SubCalls) n stage2Body
            (walkSeedFinalState G S
              (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
              (entryPos G 0) (entryByte G 0))) ∧
        WalkInv G (walkSeed G S)
          (walkSeedFinalState G S
            (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
            (entryPos G 0) (entryByte G 0)) ∧
        (∃ v : Value, WalkLoopStep (stage2Calls stage2SubCalls) G v 27)))

/-- **What a dispatch supplies, at the geometry and the stage the record gives.**
A proof of `WalkPremises` no longer has to invent a geometry and a staging: the two
constructions (`walkGeom_at_pre`, `walkStage_at_pre`) build them from the record's
precondition and the adapter's staging, so the seed's prefix, the invariant at the
loop head and the loop's step are owed at a pair the prover *is given*.  This is the
shape the dispatch's proof is written against, and it is why the two constructions
are theorems rather than fields of the premise. -/
theorem walkPremises_of_parts {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (h : ∀ (a13 : List Value) (mem : Mem) (next : Nat) (G : WalkGeom mem)
        (S : WalkStage G),
      Γ_stage2.pre a13 mem next →
      stage2StagedPre a13 mem next d c ctype cst tok s z e nkSlot nxpSlot →
      G.next0 = next →
      a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err] →
      ((G.nep = 0 ∧
          ∃ v0 : Value,
            WalkFlush (stage2Calls stage2SubCalls) v0 a13 G.nep d c ctype cst tok s z e) ∨
        (0 < G.nep ∧
        (∀ n, runFuel (stage2Calls stage2SubCalls) (3 + n) stage2Body
            (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
          runFuel (stage2Calls stage2SubCalls) n stage2Body
            (walkSeedFinalState G S
              (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
              (entryPos G 0) (entryByte G 0))) ∧
        WalkInv G (walkSeed G S)
          (walkSeedFinalState G S
            (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
            (entryPos G 0) (entryByte G 0)) ∧
        (∃ v : Value, WalkLoopStep (stage2Calls stage2SubCalls) G v 27)))) :
    WalkPremises d c ctype cst tok s z e nkSlot nxpSlot := by
  intro a13 mem next hpre hst
  obtain ⟨G, S, hnext, hargs⟩ := walkStage_at_pre hpre hst
  exact ⟨mem, G, S, hnext, hargs, h a13 mem next G S hpre hst hnext hargs⟩

/-- **The budget carries the finalisation allowance at every staging**, so the
empty stream's flush arm is inside it: the record's budget is
`32·nep + 8·n + 32·nxp + 32` and the arm costs at most the last term. -/
theorem walkBudget_ge_finalisation {mem : Mem}
    {b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat} :
    stage2FinalisationAllowance ≤
      stage2Budget [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
        .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
        .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
        .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] mem := by
  simp only [stage2Budget, stage2EntryAllowance, stage2ByteAllowance,
    stage2PositionAllowance, stage2FinalisationAllowance]
  omega

/-- **The completion at the record's own budget**, from the premises the four
obstructions name: the seed's prefix at the ABI's entry state, the invariant at the
loop head, and the loop's step.  The budget is `stage2Budget` at `a13`, which
`walkGeom_at_pre` identifies with the geometry's numbers.

The empty entry stream is a branch of its own: at `nep = 0` the entry's test takes
its zero arm and `WalkFlush` completes the run inside the finalisation allowance,
which `stage2Budget` carries at every staging (`walkBudget_ge_finalisation`).  The
other branch is the loop, and the two are exhaustive because the count is a
`Nat`. -/
theorem stage2WalkCompletes_of_premises {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (h : WalkPremises d c ctype cst tok s z e nkSlot nxpSlot) :
    Stage2WalkCompletes d c ctype cst tok s z e nkSlot nxpSlot stage2SubCalls := by
  intro a13 mem next hpre hstaged
  obtain ⟨m0, G, S, hnext, hargs, hbr⟩ := h a13 mem next hpre hstaged
  rcases hbr with ⟨hzero, v0, hflush⟩ | ⟨hn, hseed, hInv, hloop⟩
  · -- the empty entry stream: the entry's zero arm and the refusal copy
    obtain ⟨q, m, hq, hrun⟩ := hflush hzero mem next
    refine ⟨v0, m, ?_⟩
    rw [hargs] at hrun ⊢
    exact runFuel_mono_le (le_trans hq walkBudget_ge_finalisation) hrun
  · -- entries left: the seed, the invariant and the loop's step
    obtain ⟨v, hloopv⟩ := hloop
    obtain ⟨v', m, hrun⟩ :=
      walkCompletes_at_stage2Budget (calls := stage2Calls stage2SubCalls) (G := G)
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

/-! ### The run's report, from the invariant

`stage2Boundary_of_parts` consumes a `Stage2Run`: the geometry's numbers, the two
cursors as the walk left them, the refusal bit and its offset, and the two region
claims.  Every one of those is a clause of `WalkInv` at the loop's end — the
geometry's fields are `WalkGeom`'s, the cursors and the refusal are the carry's,
and the two region clauses are the invariant's `frame` and, through its `owned`
extents, the presence half.  So the report is a projection and not a premise: a
caller holding the invariant at a state holds the run.

The frames agree by definition: `Stage2Run.walkFrame`'s list is `walkWide`, which is
where `WalkInv.frame` is stated.  Presence needs one step — the carry's own list is
`[(dst, alen), (ev, evlen)]` and the extents it claims are the staging's — so each
of its entries lies inside a staged extent (`(dst, ndst0 + n + reserve)` covers the
arena's prefix at `alen ≤ ndst0 + n`, and `(ev, evcap)` covers the event stream's
at `evlen ≤ evcap`), which is the coverage `WalkInv.report` reads. -/
def Stage2Run.ofInv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (h : WalkInv G C s) {args : List Value}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]) :
    Stage2Run args m0 s.mem where
  b := G.b
  n := G.n
  ep := G.ep
  nep := G.nep
  xp := G.xp
  nxp := G.nxp
  dst := G.dst
  dstcap := G.dstcap
  ndst := G.ndst
  ev := G.ev
  evcap := G.evcap
  nev := G.nev
  err := G.err
  bs := G.bs
  ent := G.ent
  ndst0 := G.ndst0
  nev0 := G.nev0
  alen := C.alen
  evlen := C.evlen
  refusal := C.refusal
  eoff := C.eoff
  args_eq := hargs
  doc := G.doc
  tail := G.tail
  entries := G.entries
  order := G.order
  inside := G.inside
  esc := G.esc
  arenaCap := G.arenaCap
  arenaRoom := G.arenaRoom
  evCap := G.evCap
  evRoom := G.evRoom
  ndstRead := G.ndstRead
  nevRead := G.nevRead
  errBytes := G.errBytes
  maxDoc := G.maxDoc
  c := C.stage.c
  ctype := C.stage.ctype
  cst := C.stage.cst
  tok := C.stage.tok
  s := C.stage.s
  z := C.stage.z
  e := C.stage.e
  d := C.stage.d
  nkSlot := C.stage.nkSlot
  nxpSlot := C.stage.nxpSlot
  staged := C.stage.separate
  arenaGe := h.alen_ge
  arenaLe := h.alen_le
  evGe := by rw [h.evlen_eq]; exact Nat.le_add_right _ _
  evLe := h.evlen_le
  reserve := (Nat.add_le_add_right h.alen_le stage2ArenaReserve).trans G.arenaRoom
  next0 := G.next0
  watermark := G.watermark
  walkPresent := by
    intro a ha
    have hale := h.alen_le
    have hevle : C.evlen ≤ G.evcap := le_trans h.evlen_le G.evRoom
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    simp only [walkPresent, stage2ReportScratch] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr1
      · refine present_of_hasBytes (h.owned (G.dst, G.ndst0 + G.n + stage2ArenaReserve)
          (by simp [walkStaged])) hlo ?_
        exact Nat.lt_of_lt_of_le hhi (Nat.add_le_add_left
          (le_trans hale (Nat.le_add_right _ _)) _)
      · rcases List.mem_cons.mp hr1 with rfl | hnil
        · refine present_of_hasBytes (h.owned (G.ev, G.evcap) (by simp [walkStaged]))
            hlo ?_
          exact Nat.lt_of_lt_of_le hhi (Nat.add_le_add_left hevle _)
        · exact absurd hnil (by simp)
    · refine present_of_hasBytes (h.owned r ?_) hlo hhi
      simp only [walkStaged, stage2ReportScratch]
      exact List.mem_append_right _ hr
  walkFrame := by simpa only [walkWide, walkPresent] using h.frame
  dSep := C.stage.dSep
  offLe := fun _ => h.eoff_le
  dstcapLt := G.dstcapLt
  evcapLt := G.evcapLt
  nepLt := by
    have hle := G.nep_le
    have hdoc := G.maxDoc
    simp only [stage2MaxDocument] at hdoc
    omega
  nxpLt := G.nxpLt
  bPos := G.bPos
  bLt := G.bLt
  epLt := G.epLt

/-- **A behaviour of a completing run is the completion's outcome.**  `BehFromState`
quantifies over the fuel, and the fuel does not select the result
(`runFuel_outcome_unique`): two budgets that both produce an outcome produce the
same one.  So beside a completion at `o`, the `.ub` behaviour is impossible and
every returning one is that same outcome.

This is the step that turns the completion conjunct into the post's `∀` over
behaviours: `stage2Post` is a match on the outcome, so once the outcome is the
completion's the post is the boundary `stage2Run_boundary` supplies. -/
theorem stage2Post_of_completion {calls : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {sE : State} {B : Nat} {oGood : Outcome}
    (hcom : runFuel calls B stage2Body sE = some oGood)
    (hgood : stage2Post args mem next oGood) :
    ∀ o, BehFromState calls stage2Body sE o → stage2Post args mem next o := by
  intro o hbeh
  rcases hbeh with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hEq : oGood = Outcome.ub := (runFuel_outcome_unique hn hcom).symm
    rw [hEq] at hgood
    exact hgood.elim
  · have hEq := runFuel_outcome_unique hn hcom
    rw [hEq]
    exact hgood

/-- **The post, from a completion at the report's memory.**  `stage2Run_boundary`
gives the boundary at the outcome `(.int 64 verdict)` in the memory the wrapper's
stores leave (`stage2Report`), and `stage2Post_of_completion` carries it from that
one outcome to every behaviour of the run.  So the post half's two inputs are the
boundary at the report — which is a projection of the invariant
(`Stage2Run.ofInv`) — and the completion conjunct's own outcome, read at
`stage2Report`.

What this states is that the post needs nothing else: the run's other outcomes are
excluded by the fuel's uniqueness, and the boundary is the record's. -/
theorem stage2Post_of_run {args : List Value} {mem m0 : Mem} {B : Nat}
    {calls : Calls} {sE : State}
    (hrun : Stage2Run args mem m0)
    (hcom : runFuel calls B stage2Body sE = some
      (Outcome.ret (some (.int 64 (stage2Verdict hrun.refusal)))
        (stage2Report m0 hrun.ndst hrun.nev hrun.err hrun.alen hrun.evlen
          hrun.refusal hrun.eoff))) :
    ∀ o, BehFromState calls stage2Body sE o → stage2Post args mem hrun.next0 o :=
  stage2Post_of_completion hcom (stage2Run_boundary hrun)

/-- **The obligation from the premises and its post.**  `Stage2WalkObligation` is
the completion conjunct beside the post (`stage2WalkObligation_iff_completion`), so
a dispatch that supplies `WalkPremises` and the record's post rule has the
obligation.  Naming the two is the point: the completion is this module's, and the
post half — the run's own region claim at the outcome — is not read here. -/
theorem stage2WalkObligation_of_premises {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (h : WalkPremises d c ctype cst tok s z e nkSlot nxpSlot)
    (hpost : ∀ args mem next,
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).pre args mem next →
      ∀ o, BehFromState (stage2Calls stage2SubCalls) stage2Body
          (EntryState stage2Body args mem next) o →
        (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post args mem next o) :
    Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot :=
  (stage2WalkObligation_iff_completion d c ctype cst tok s z e nkSlot nxpSlot).2
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

#print axioms LeanLLVM.Refinement.WalkScope.Stage2Run.ofInv
#print axioms LeanLLVM.Refinement.WalkScope.stage2Post_of_completion
#print axioms LeanLLVM.Refinement.WalkScope.stage2Post_of_run
#print axioms LeanLLVM.Refinement.WalkScope.walkPhiBrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkPhiCondbrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkStackMarkerStep
#print axioms LeanLLVM.Refinement.WalkScope.walkTwoLoadAddIcmpStep
#print axioms LeanLLVM.Refinement.WalkScope.walkAddIcmpBrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkPhiGepLoadBrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkDoc_byte
#print axioms LeanLLVM.Refinement.WalkScope.walkWide_doc_out
#print axioms LeanLLVM.Refinement.WalkScope.walkWide_outside
#print axioms LeanLLVM.Refinement.WalkScope.execTerm_condbr_bit
#print axioms LeanLLVM.Refinement.WalkScope.walkCondEnd349Step
#print axioms LeanLLVM.Refinement.WalkScope.walkGepLoadBrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkIcmpBrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkBrStep
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock99_at
#print axioms LeanLLVM.Refinement.WalkScope.walkCondbrStep
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen488Step
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen492Step
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen485Step
#print axioms LeanLLVM.Refinement.WalkScope.walkIfEnd490Step
#print axioms LeanLLVM.Refinement.WalkScope.walkBackFalse_step
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
#print axioms LeanLLVM.Refinement.WalkScope.walkBudget_ge_finalisation
#print axioms LeanLLVM.Refinement.WalkScope.WalkFlush
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedPrefix_entry
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedPrefix_entry_geometry
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkCompletes_of_premises
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkObligation_of_premises

end WalkScope

end LeanLLVM.Refinement
