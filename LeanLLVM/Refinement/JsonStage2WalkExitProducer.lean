/-
The walk's exit, produced from the last entry's facts.

`WalkExit` (`JsonStage2WalkAssembly`) asks for a run from the loop head to a return:
the last entry's dispatch to `cleanup478.i`, then the merge's false edge and one of the
exit's three tails.  This module composes it from the pieces that are already proved —
`hlast_toMerge` for the head path, `walkExitTailExit` / `walkExitTailRefuse` /
`walkExitTailRefuse488` for the tails — and states exactly what the composition leaves to
its caller.

## What the producer concludes

`walkExit_ofLastFacts` is the composition, and `walkExit_at_stage2Calls` states it as
`WalkExit (stage2Calls stage2SubCalls) G v` at the segment-calls the layer uses.  Two
points about `WalkExit`'s statement are recorded here as well as in its own docstring —
one a correction, one a deletion:

* **The index conjunct.**  `WalkExit` originally concluded `Cend.k = G.nep`, and that
  form is false of the model: the merge `cleanup478.i` binds `%k.2.i` and `%sp.i.1` and
  leaves `%k.0.i249` alone (`cleanup478Block`), while `WalkInv.blockIndex` reads the
  carry's index off `%k.0.i249`, which only the header `while.body.i` binds
  (`JsonStage2IR`).  So `hlast_toMerge`'s target carry has `Cend.k = C.k`, and beside the
  premise `C.k + 1 = G.nep` the old conjunct contradicted `WalkInv`.  The statement now
  reads `Cend.k + 1 = G.nep` — the last entry's own `hlastK` — which is what the run
  establishes.  `WalkExit`'s only consumer (`walkLoopStep_of_dispatch_exit`) discards
  `Cend` and `sEnd`, so nothing read the old form.

* **The arena word was deleted, because it was inert.**  `WalkExit` used to take the word
  at the head as a premise and assert the same equality at `cleanup478.i`, and this
  producer carried both: the premise was never read, and the post clause existed only to
  be discarded.  The word is also not a fact of the loop head — the reserve advances the
  carry by a token's document extent while the write-back stores the decoded length, so a
  body that escapes leaves the slot below `C.alen` and nothing lowers `alen` again
  (`JsonStage2WalkArenaWord`).  Both clauses are gone; `WalkInv.log_alen`'s existential —
  *some* `a` at or below the carry — is what `WalkInv G Cend sEnd` already carries, so
  restating it here would duplicate the invariant.

## What the producer leaves to its caller

The tails' premises are the caller's, as `JsonStage2WalkAssembly` records: the copy
blocks' `denoteCode` equations (four configurations time out at 1M and 4M heartbeats),
the root-done word, the two register words the copy reads (`%e`, `%4`), and the two
pointer registers `%z` and `%s` that no `WalkInv` field binds.  The three routers below
take the route's own premises and pass everything `WalkInv` and the bundle do supply —
`%nep`, `%inc.i`, `%sp.i.0248`, `%root_done.i`, `%e`, `%4`, and the composite states'
lookups — through, so a caller sees only the facts it holds.

`%z` and `%s` are the one place where `WalkExit`'s shape and this producer's disagree.
`WalkExit` names them at the loop head, where its `∀` binds the state, because a premise
that only the terminal block reads belongs to the terminal statement rather than to
`WalkInv` (the argument `hinner` gets).  The producer reads them at `cleanup478.i`, the
state the tails consume them at, and `walkExit_at_stage2Calls` therefore takes them from
the caller's merge-state supplier and drops the head-level pair: carrying a register along
the head path is the one head-path obligation this layer does not discharge, since a
`WalkSegment` exposes neither the run's blocks nor their stores.

## The price

`walkExitPrice`: the head path's twenty steps (`hlast_toMerge`'s count) plus the tail's,
against `walkPotential G C + 27`.  At the last entry `G.nep - C.k = 1`, so the potential
is at least one entry allowance and the tail's `q ≤ 25` fits beside it.  The exit does
*not* charge against the document bytes it has left to reach: `walkPotential`'s byte term
is `8 · (G.n - entryPos G C.k)`, and the head path's price at the last entry is
`entryPos G G.nep = 0` (`entryPos_nep`), so the byte credit the dispatch spent is not
recovered here.  Whether the exit should charge against the remaining document bytes is a
statement-shape question for the layer that owns `WalkPotential`, and it is not decided
here.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntrySteps

namespace WalkScope

/-! ### The tail's run, named -/

/-- **The exit tail's run**: the count, the three states, and the two terminal steps, at
the shape `WalkExit` states its tail. -/
def ExitTail (calls : Calls) (s : State) (v : Value) : Prop :=
  ∃ (q : Nat) (s1 s2 sret : State),
    (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
    q + 2 ≤ 27 ∧
    step calls stage2Body s1 = .jump s2 ∧
    step calls stage2Body s2 = .ret (some v) sret

/-! ### The head path's count

`hlast_toMerge` states it as a literal; the price needs the number. -/

/-- The head path's count: the six-block fall-through, the seam, the class-C span, the
tail's three links, the scan's three, the latch's exit and the merge. -/
theorem hlastMergeCount : ((((((6 + 1) + 5) + 3) + 3) + 1) + 1) = 20 := by decide

/-- **The exit's price.**  Twenty steps to the merge and the tail's own count inside the
potential the last entry still holds plus the finalisation allowance. -/
theorem walkExitPrice {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {q : Nat}
    (hlast : C.k + 1 = G.nep) (hq : q + 2 ≤ 27) :
    20 + q ≤ walkPotential G C + 27 := by
  have hk : G.nep - C.k = 1 := by omega
  simp only [walkPotential, stage2EntryAllowance, stage2ByteAllowance]
  omega

/-! ### The exit's states do not bind the registers the tails read

Each of the exit's state constructors is a bind chain over the merge's state; a name none
of them binds reads through to it.  The two copy blocks' dst sets are below them.
-/

/-- A name `exitS₁` does not bind reads through it. -/
theorem exitS₁_env' {s : State} {spv k2 : Nat} {n : String}
    (h1 : "%cmp.i" ≠ n) (h2 : "%k.2.i" ≠ n) (h3 : "%sp.i.1" ≠ n) :
    lookupName (exitS₁ s spv k2).env n = lookupName s.env n := by
  simp only [exitS₁, State.bind]
  rw [lookupName_cons_ne (k := "%cmp.i") (n := n) _ _ h1,
      lookupName_cons_ne (k := "%k.2.i") (n := n) _ _ h2,
      lookupName_cons_ne (k := "%sp.i.1") (n := n) _ _ h3]

/-- The twin at `exitS₂`. -/
theorem exitS₂_env' {s : State} {spv : Nat} {n : String} (h1 : "%48" ≠ n) :
    lookupName (exitS₂ s spv).env n = lookupName s.env n := by
  simp only [exitS₂, State.bind]
  rw [lookupName_cons_ne (k := "%48") (n := n) _ _ h1]

/-- The twin at `exitS₂r`. -/
theorem exitS₂r_env' {s : State} {spv : Nat} {n : String} (h1 : "%48" ≠ n) :
    lookupName (exitS₂r s spv).env n = lookupName s.env n := by
  simp only [exitS₂r, State.bind]
  rw [lookupName_cons_ne (k := "%48") (n := n) _ _ h1]

/-- The twin at `exitS₃`. -/
theorem exitS₃_env' {s : State} {rv : BitVec 32} {n : String}
    (h1 : "%.pr" ≠ n) (h2 : "%tobool491.not.i" ≠ n) :
    lookupName (exitS₃ s rv).env n = lookupName s.env n := by
  simp only [exitS₃, State.bind]
  rw [lookupName_cons_ne (k := "%tobool491.not.i") (n := n) _ _ h2,
      lookupName_cons_ne (k := "%.pr") (n := n) _ _ h1]

/-- The twin at `exitS₃r`. -/
theorem exitS₃r_env' {s : State} {rv : BitVec 32} {n : String}
    (h1 : "%.pr" ≠ n) (h2 : "%tobool491.not.i" ≠ n) :
    lookupName (exitS₃r s rv).env n = lookupName s.env n := by
  simp only [exitS₃r, State.bind]
  rw [lookupName_cons_ne (k := "%tobool491.not.i") (n := n) _ _ h2,
      lookupName_cons_ne (k := "%.pr") (n := n) _ _ h1]

/-- The twin at `exitS₅`. -/
theorem exitS₅_env' {s : State} {e v : Nat} {n : String} (h1 : "%off1.i.i117" ≠ n) :
    lookupName (exitS₅ s e v).env n = lookupName s.env n := by
  simp only [exitS₅]
  rw [lookupName_cons_ne (k := "%off1.i.i117") (n := n) _ _ h1]

/-- The twin at `exitS₅r`. -/
theorem exitS₅r_env' {s : State} {e v : Nat} {n : String} (h1 : "%off1.i.i115" ≠ n) :
    lookupName (exitS₅r s e v).env n = lookupName s.env n := by
  simp only [exitS₅r]
  rw [lookupName_cons_ne (k := "%off1.i.i115") (n := n) _ _ h1]

/-- The exit's copy block binds `%49` and `%50` and nothing else. -/
theorem walkExitBlock_keeps (n : String) (h49 : "%49" ≠ n) (h50 : "%50" ≠ n) :
    ∀ i ∈ walkExitBlock.instrs, i.dst? ≠ some n := by
  intro i hi
  simp only [walkExitBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; exact h49 (Option.some.inj hh)
  · intro hh; cases hh
  · intro hh; exact h50 (Option.some.inj hh)
  · intro hh; cases hh

/-- The refusal's copy block binds `%51`, `%52`, `%off` and `%53` and nothing else. -/
theorem walkIfThenBlock_keeps (n : String) (h51 : "%51" ≠ n) (h52 : "%52" ≠ n)
    (hoff : "%off" ≠ n) (h53 : "%53" ≠ n) :
    ∀ i ∈ walkIfThenBlock.instrs, i.dst? ≠ some n := by
  intro i hi
  simp only [walkIfThenBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; cases hh
  · intro hh; exact h51 (Option.some.inj hh)
  · intro hh; cases hh
  · intro hh; exact h52 (Option.some.inj hh)
  · intro hh; cases hh
  · intro hh; exact hoff (Option.some.inj hh)
  · intro hh; exact h53 (Option.some.inj hh)
  · intro hh; cases hh

/-! ### The three tails, from the merge -/

/-- **The exit's own route**, `s2_walk.exit` with the stack empty and the root-done word
zero: `walkExitTailExit` at the bundle's merge state.  `WalkInv` and the bundle supply
`%nep`, `%inc.i`, `%sp.i.0248`, `%root_done.i`, `%e`, `%4` and the composite states'
lookups; the caller supplies the root-done word, its two polarities, `%z`/`%s`, and the
copy's equation. -/
theorem walkExitTailRun_exit {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (f : HlastFacts G C s)
    (hz : lookupName (hlastMergeF f).env "%z" = some (.ptr C.stage.z))
    (hs : lookupName (hlastMergeF f).env "%s" = some (.ptr C.stage.s))
    (hsp0 : evalICmp .eq (BitVec.ofNat 32 f.spv) (BitVec.ofNat 32 0) = 1)
    {rv : BitVec 32} {s₃ : State}
    (hrv : readBytes (hlastMergeF f).mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (hrv0 : evalICmp .eq rv (BitVec.ofNat 32 0) = 0)
    (hden : denoteCode (stage2Calls stage2SubCalls) walkExitBlock.instrs
      (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv) = some s₃)
    (hpc₃ : s₃.pc = (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv).pc) :
    ExitTail (stage2Calls stage2SubCalls) (hlastMergeF f) (.int 64 (BitVec.ofNat 64 1)) := by
  obtain ⟨-, hinv⟩ := hlast_toMerge G C s hInv hhead f
  have hroot : lookupName (hlastMergeF f).env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hinv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have he₃ : lookupName (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv).env "%e"
      = some (.ptr C.stage.e) :=
    (exitS₃_env' (n := "%e") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%e") (by decide)).trans
        ((exitS₁_env' (n := "%e") (by decide) (by decide) (by decide)).trans f.heM))
  have hz₃ : lookupName (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv).env "%z"
      = some (.ptr C.stage.z) :=
    (exitS₃_env' (n := "%z") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%z") (by decide)).trans
        ((exitS₁_env' (n := "%z") (by decide) (by decide) (by decide)).trans hz))
  have hs₃ : lookupName (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv).env "%s"
      = some (.ptr C.stage.s) :=
    (exitS₃_env' (n := "%s") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%s") (by decide)).trans
        ((exitS₁_env' (n := "%s") (by decide) (by decide) (by decide)).trans hs))
  have he' : lookupName
      (exitS₄ (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv) s₃).env "%e"
      = some (.ptr C.stage.e) := by
    show lookupName s₃.env "%e" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkExitBlock.instrs "%e"
      (walkExitBlock_keeps "%e" (by decide) (by decide)) _ _ hden]
    exact he₃
  have hz' : lookupName
      (exitS₄ (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv) s₃).env "%z"
      = some (.ptr C.stage.z) := by
    show lookupName s₃.env "%z" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkExitBlock.instrs "%z"
      (walkExitBlock_keeps "%z" (by decide) (by decide)) _ _ hden]
    exact hz₃
  have hs' : lookupName
      (exitS₄ (exitS₃ (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv) s₃).env "%s"
      = some (.ptr C.stage.s) := by
    show lookupName s₃.env "%s" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkExitBlock.instrs "%s"
      (walkExitBlock_keeps "%s" (by decide) (by decide)) _ _ hden]
    exact hs₃
  have hk2' : f.k2 < 2 ^ 64 := by rw [f.hterm]; exact f.nepv.isLt
  have hguard' : f.nepv.toNat ≤ f.k2 := by rw [f.hterm]
  obtain ⟨q, s1, s2, sret, hrun, hq, hjump, hret⟩ :=
    walkExitTailExit (sub := stage2SubCalls) (s := hlastMergeF f) (p := "if.end473.i")
      (spv := f.spv) (k2 := f.k2) (spOp := .reg "%sp.i.0248") (kOp := .reg "%inc.i")
      (nepv := f.nepv) (rd := G.next0 + 8) (rv := rv) (s₃ := s₃)
      (v := BitVec.ofNat 64 1) (bit := BitVec.ofNat 64 1)
      rfl rfl (by decide) f.hspvM (by decide) f.hk2 f.hnepM hk2' hguard' hsp0 hroot hrv hrv0
      hden hpc₃ he' hz' hs' (by decide) (by decide)
  exact ⟨q, s1, s2, sret, hrun, hq, hjump, hret⟩

/-- **The refusal through `if.then492.i`**: the stack empty and the root-done word set.
The refusal record's pointer `%e` and the word `%4` are the bundle's; the copy's equation
is the caller's. -/
theorem walkExitTailRun_refuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (f : HlastFacts G C s)
    (hz : lookupName (hlastMergeF f).env "%z" = some (.ptr C.stage.z))
    (hs : lookupName (hlastMergeF f).env "%s" = some (.ptr C.stage.s))
    (hsp0 : evalICmp .eq (BitVec.ofNat 32 f.spv) (BitVec.ofNat 32 0) = 1)
    {rv : BitVec 32} {s₂ : State}
    (hrv : readBytes (hlastMergeF f).mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (hrv1 : evalICmp .eq rv (BitVec.ofNat 32 0) = 1)
    (hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs
      (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv) C.stage.e f.v)
      = some s₂)
    (hpc₂ : s₂.pc = (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
      C.stage.e f.v).pc) :
    ExitTail (stage2Calls stage2SubCalls) (hlastMergeF f) (.int 64 (BitVec.ofNat 64 0)) := by
  obtain ⟨-, hinv⟩ := hlast_toMerge G C s hInv hhead f
  have hroot : lookupName (hlastMergeF f).env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hinv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have he₃ : lookupName
      (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv).env "%e"
      = some (.ptr C.stage.e) :=
    (exitS₃r_env' (n := "%e") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%e") (by decide)).trans
        ((exitS₁_env' (n := "%e") (by decide) (by decide) (by decide)).trans f.heM))
  have h4₃ : lookupName
      (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv).env "%4"
      = some (.int 64 (BitVec.ofNat 64 f.v)) :=
    (exitS₃r_env' (n := "%4") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%4") (by decide)).trans
        ((exitS₁_env' (n := "%4") (by decide) (by decide) (by decide)).trans f.h4M))
  have he₂ : lookupName
      (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
        C.stage.e f.v).env "%e" = some (.ptr C.stage.e) :=
    (exitS₅_env' (n := "%e") (by decide)).trans he₃
  have hz₂ : lookupName
      (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
        C.stage.e f.v).env "%z" = some (.ptr C.stage.z) :=
    (exitS₅_env' (n := "%z") (by decide)).trans
      ((exitS₃r_env' (n := "%z") (by decide) (by decide)).trans
        ((exitS₂_env' (n := "%z") (by decide)).trans
          ((exitS₁_env' (n := "%z") (by decide) (by decide) (by decide)).trans hz)))
  have hs₂ : lookupName
      (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
        C.stage.e f.v).env "%s" = some (.ptr C.stage.s) :=
    (exitS₅_env' (n := "%s") (by decide)).trans
      ((exitS₃r_env' (n := "%s") (by decide) (by decide)).trans
        ((exitS₂_env' (n := "%s") (by decide)).trans
          ((exitS₁_env' (n := "%s") (by decide) (by decide) (by decide)).trans hs)))
  have he' : lookupName
      (exitS₄ (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
        C.stage.e f.v) s₂).env "%e" = some (.ptr C.stage.e) := by
    show lookupName s₂.env "%e" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThenBlock.instrs "%e"
      (walkIfThenBlock_keeps "%e" (by decide) (by decide) (by decide) (by decide)) _ _ hden]
    exact he₂
  have hz' : lookupName
      (exitS₄ (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
        C.stage.e f.v) s₂).env "%z" = some (.ptr C.stage.z) := by
    show lookupName s₂.env "%z" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThenBlock.instrs "%z"
      (walkIfThenBlock_keeps "%z" (by decide) (by decide) (by decide) (by decide)) _ _ hden]
    exact hz₂
  have hs' : lookupName
      (exitS₄ (exitS₅ (exitS₃r (exitS₂ (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) rv)
        C.stage.e f.v) s₂).env "%s" = some (.ptr C.stage.s) := by
    show lookupName s₂.env "%s" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThenBlock.instrs "%s"
      (walkIfThenBlock_keeps "%s" (by decide) (by decide) (by decide) (by decide)) _ _ hden]
    exact hs₂
  have hk2' : f.k2 < 2 ^ 64 := by rw [f.hterm]; exact f.nepv.isLt
  have hguard' : f.nepv.toNat ≤ f.k2 := by rw [f.hterm]
  obtain ⟨q, s1, s₂', sret, hrun, hq, hjump, hret⟩ :=
    walkExitTailRefuse (sub := stage2SubCalls) (s := hlastMergeF f) (p := "if.end473.i")
      (spv := f.spv) (k2 := f.k2) (spOp := .reg "%sp.i.0248") (kOp := .reg "%inc.i")
      (nepv := f.nepv) (rd := G.next0 + 8) (rv := rv) (s₂ := s₂) (e := C.stage.e)
      (v := f.v) (w := BitVec.ofNat 64 0) (bit := BitVec.ofNat 64 0)
      rfl rfl (by decide) f.hspvM (by decide) f.hk2 f.hnepM hk2' hguard' hsp0 hroot hrv hrv1
      he₃ h4₃ f.hv64 hden hpc₂ he' hz' hs' (by decide) (by decide)
  exact ⟨q, s1, s₂', sret, hrun, hq, hjump, hret⟩

/-- **The refusal through `if.then488.i`**: the stack non-empty, so the merge's false arm
takes the refusal copy without the root-done test. -/
theorem walkExitTailRun_refuse488 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (f : HlastFacts G C s)
    (hz : lookupName (hlastMergeF f).env "%z" = some (.ptr C.stage.z))
    (hs : lookupName (hlastMergeF f).env "%s" = some (.ptr C.stage.s))
    (hspn : evalICmp .eq (BitVec.ofNat 32 f.spv) (BitVec.ofNat 32 0) = 0)
    {s₂ : State}
    (hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs
      (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v) = some s₂)
    (hpc₂ : s₂.pc = (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv)
      C.stage.e f.v).pc) :
    ExitTail (stage2Calls stage2SubCalls) (hlastMergeF f) (.int 64 (BitVec.ofNat 64 0)) := by
  obtain ⟨-, hinv⟩ := hlast_toMerge G C s hInv hhead f
  have he₂ : lookupName
      (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv).env "%e" = some (.ptr C.stage.e) :=
    (exitS₂r_env' (n := "%e") (by decide)).trans
      ((exitS₁_env' (n := "%e") (by decide) (by decide) (by decide)).trans f.heM)
  have h4₂ : lookupName
      (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv).env "%4"
      = some (.int 64 (BitVec.ofNat 64 f.v)) :=
    (exitS₂r_env' (n := "%4") (by decide)).trans
      ((exitS₁_env' (n := "%4") (by decide) (by decide) (by decide)).trans f.h4M)
  have he₅ : lookupName
      (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v).env "%e"
      = some (.ptr C.stage.e) :=
    (exitS₅r_env' (n := "%e") (by decide)).trans he₂
  have hz₅ : lookupName
      (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v).env "%z"
      = some (.ptr C.stage.z) :=
    (exitS₅r_env' (n := "%z") (by decide)).trans
      ((exitS₂r_env' (n := "%z") (by decide)).trans
        ((exitS₁_env' (n := "%z") (by decide) (by decide) (by decide)).trans hz))
  have hs₅ : lookupName
      (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v).env "%s"
      = some (.ptr C.stage.s) :=
    (exitS₅r_env' (n := "%s") (by decide)).trans
      ((exitS₂r_env' (n := "%s") (by decide)).trans
        ((exitS₁_env' (n := "%s") (by decide) (by decide) (by decide)).trans hs))
  have he' : lookupName
      (exitS₄ (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v) s₂).env
      "%e" = some (.ptr C.stage.e) := by
    show lookupName s₂.env "%e" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThenBlock.instrs "%e"
      (walkIfThenBlock_keeps "%e" (by decide) (by decide) (by decide) (by decide)) _ _ hden]
    exact he₅
  have hz' : lookupName
      (exitS₄ (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v) s₂).env
      "%z" = some (.ptr C.stage.z) := by
    show lookupName s₂.env "%z" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThenBlock.instrs "%z"
      (walkIfThenBlock_keeps "%z" (by decide) (by decide) (by decide) (by decide)) _ _ hden]
    exact hz₅
  have hs' : lookupName
      (exitS₄ (exitS₅r (exitS₂r (exitS₁ (hlastMergeF f) f.spv f.k2) f.spv) C.stage.e f.v) s₂).env
      "%s" = some (.ptr C.stage.s) := by
    show lookupName s₂.env "%s" = _
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThenBlock.instrs "%s"
      (walkIfThenBlock_keeps "%s" (by decide) (by decide) (by decide) (by decide)) _ _ hden]
    exact hs₅
  have hk2' : f.k2 < 2 ^ 64 := by rw [f.hterm]; exact f.nepv.isLt
  have hguard' : f.nepv.toNat ≤ f.k2 := by rw [f.hterm]
  obtain ⟨q, s1, s₂', sret, hrun, hq, hjump, hret⟩ :=
    walkExitTailRefuse488 (sub := stage2SubCalls) (s := hlastMergeF f) (p := "if.end473.i")
      (spv := f.spv) (k2 := f.k2) (spOp := .reg "%sp.i.0248") (kOp := .reg "%inc.i")
      (nepv := f.nepv) (s₂ := s₂) (e := C.stage.e) (v := f.v)
      (w := BitVec.ofNat 64 0) (bit := BitVec.ofNat 64 0)
      rfl rfl (by decide) f.hspvM (by decide) f.hk2 f.hnepM hk2' hguard' hspn
      he₂ h4₂ f.hv64 hden hpc₂ he' hz' hs' (by decide) (by decide)
  exact ⟨q, s1, s₂', sret, hrun, hq, hjump, hret⟩

/-! ### The producer -/

/-- **The exit, from the last entry's facts and the tail's run.**  `WalkExit`'s body, with
the merge's index conjunct as the last entry's own `hlastK` states it. -/
theorem walkExit_ofLastFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hlast : C.k + 1 = G.nep)
    (f : HlastFacts G C s)
    {v : Value}
    (htail : ExitTail (stage2Calls stage2SubCalls) (hlastMergeF f) v) :
    ∃ (Cend : WalkCarry G) (sEnd : State), WalkInv G Cend sEnd ∧
      Cend.block = "cleanup478.i" ∧ Cend.k + 1 = G.nep ∧
      ∃ (q₁ q₂ : Nat) (s1 s2 sret : State),
        (∀ n, runFuel (stage2Calls stage2SubCalls) (q₁ + n) stage2Body s
          = runFuel (stage2Calls stage2SubCalls) n stage2Body sEnd) ∧
        q₁ + q₂ ≤ walkPotential G C + 27 ∧
        (∀ n, runFuel (stage2Calls stage2SubCalls) (q₂ + n) stage2Body sEnd
          = runFuel (stage2Calls stage2SubCalls) n stage2Body s1) ∧
        step (stage2Calls stage2SubCalls) stage2Body s1 = .jump s2 ∧
        step (stage2Calls stage2SubCalls) stage2Body s2 = .ret (some v) sret := by
  obtain ⟨hseg, hinv⟩ := hlast_toMerge G C s hInv hhead f
  obtain ⟨q, s1, s2, sret, hrun, hq, hjump, hret⟩ := htail
  refine ⟨hlastMergeCF f, hlastMergeF f, hinv, rfl, ?_,
    ((((((6 + 1) + 5) + 3) + 3) + 1) + 1), q, s1, s2, sret, hseg.run, ?_, hrun, hjump, hret⟩
  · show C.k + 1 = G.nep
    exact hlast
  · rw [hlastMergeCount]
    exact walkExitPrice hlast hq

/-- **`WalkExit` at the segment calls**: the producer's composition, stated in the
assembly's own shape.  The last entry's bundle and the tail's run are the caller's, at the
merge state each is read at; the head-level `%z`/`%s` premises `WalkExit` carries are
dropped here, because the producer reads the two registers at the merge and the head
path's register tracking is a separate obligation. -/
theorem walkExit_at_stage2Calls {m0 : Mem} (G : WalkGeom m0) {v : Value}
    (hf : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 = G.nep → HlastFacts G C s)
    (htail : ∀ (C : WalkCarry G) (s : State) (f : HlastFacts G C s),
      ExitTail (stage2Calls stage2SubCalls) (hlastMergeF f) v) :
    WalkExit (stage2Calls stage2SubCalls) G v := by
  intro C s hInv hhead hlast _hz _hs
  exact walkExit_ofLastFacts G C s hInv hhead hlast (hf C s hInv hhead hlast)
    (htail C s (hf C s hInv hhead hlast))

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.hlastMergeCount
#print axioms LeanLLVM.Refinement.WalkScope.walkExitPrice
#print axioms LeanLLVM.Refinement.WalkScope.walkExitBlock_keeps
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThenBlock_keeps
#print axioms LeanLLVM.Refinement.WalkScope.walkExitTailRun_exit
#print axioms LeanLLVM.Refinement.WalkScope.walkExitTailRun_refuse
#print axioms LeanLLVM.Refinement.WalkScope.walkExitTailRun_refuse488
#print axioms LeanLLVM.Refinement.WalkScope.walkExit_ofLastFacts
#print axioms LeanLLVM.Refinement.WalkScope.walkExit_at_stage2Calls

end WalkScope

end LeanLLVM.Refinement
