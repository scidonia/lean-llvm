/-
The last-entry bundle's domain, and the document it excludes.

`HlastFacts` (`JsonStage2WalkDispatchWitnessHlast`) requires two class bits on the head
byte:

```
evalICmp .slt (hlastByte G C) (ofNat 8 125) = 0
evalICmp .eq  (hlastByte G C) (ofNat 8 125) = 0
```

`icmp slt i8` is the *signed* order, so in an eight-bit word the first bit clear says
the byte is at least 125 in that order — one of 125, 126, 127 — and the second removes
125.  The bundle therefore describes the bytes **126 and 127**, the two invalid UTF-8
leads.  That is one arm of the head's switch (`NodeBlock17 → LeafBlock15 →
sw.default.i`), not a property of a last entry.

`WalkLoopEnd.hlast` (`JsonStage2WalkPremisesOfStaging`) asked every last-entry head
state for `HlastResidue`, whose `hlt125`/`hne125` are those same two bits.  So the
residue was demanded at states where it is false, and the layer's only consumer
(`WalkLoopEnd.facts` → `WalkLoopStepThree`) was vacuous away from the two invalid bytes.

This module states the refutation at a real input rather than at a hand-built state.
The document is the one-byte JSON scalar `0`: one entry, at position zero, whose head
byte is `0x30 = 48`.  The *seed* theorems establish reachability — `walkSeed_block`,
`walkSeedInvariant_geometry` at the record's own staging — and the byte is the
document's, read through `WalkGeom.doc`, so the class bits are facts about the staged
memory and not about a term chosen here.

The shape of the result, in the order it is proved:

* `ZeroDocument` — the staged document `0` and its single entry, as the two reads and
  the two counts;
* `hlastByte_zero` — the head byte is `48` (from `WalkGeom.doc`, `WalkGeom.entries`
  and `WalkGeom.inside`'s position zero);
* `zeroDocument_class_false` — the bundle's `slt 125` bit is `1` at that byte;
* `zeroDocument_residue_false` — hence `HlastResidue G (walkSeed G S) s` is empty;
* `zeroDocument_seededInv` — the seeded head is reachable and invariant-holding, from
  `walkSeedInvariant_geometry` at the record's staging;
* `zeroDocument_no_walkLoopEnd` — so `WalkLoopEnd G` has no inhabitant at this
  staging.  The old universal last-entry residue was not merely strong: it was false
  of an admitted document.

The refutation is *about the input*, and it is what the exhaustive dispatch in
`JsonStage2WalkDispatchArms` replaces: the last entry's class is the head byte's
switch arm, and every arm owns its premises.
-/
import LeanLLVM.Refinement.JsonStage2WalkPremisesOfStaging
import LeanLLVM.Refinement.JsonStage2WalkSeedRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

namespace WalkScope

/-! ### The document `0`, as the staging hands it over -/

/-- **The one-byte document `0` and its single entry.**  The two reads are the staged
memory's (`WalkGeom.doc` and `WalkGeom.entries`), the two counts are the ABI's, and the
document's byte is `0x30`, the JSON scalar `0`'s only character.  `entries` says the
entry stream holds exactly one lane and `laneZero` that it is zero, so the entry is at
the document's first byte. -/
structure ZeroDocument {m0 : Mem} (G : WalkGeom m0) : Prop where
  /-- The document is one byte long. -/
  len : G.n = 1
  /-- The entry stream holds one entry. -/
  count : G.nep = 1
  /-- The document's bytes are `0x30`. -/
  bytes : readBytes m0 G.b 1 = some [48]
  /-- The entry stream's lane is zero. -/
  lane : readLanes32 m0 G.ep 1 = some [0]

/-- The document's byte list is the read's: `WalkGeom.doc` at the length `len`. -/
theorem ZeroDocument.bs {m0 : Mem} {G : WalkGeom m0} (h : ZeroDocument G) :
    G.bs = [48] := by
  have hread : readBytes m0 G.b G.n = some [48] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The entry stream's lanes are the read's: `WalkGeom.entries` at the count `count`. -/
theorem ZeroDocument.ent {m0 : Mem} {G : WalkGeom m0} (h : ZeroDocument G) :
    G.ent = [0] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0] := by rw [h.count]; exact h.lane
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The one entry's position is zero: the lane list is `[0]`. -/
theorem ZeroDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0} (h : ZeroDocument G) :
    entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The document's byte at the entry is `0x30`: the byte list is `[48]`. -/
theorem ZeroDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0} (h : ZeroDocument G) :
    entryByte G 0 = 48 := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [48] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- **The seeded head's byte is `48`.**  The seed's index is zero, and the byte is the
document's at the entry's position. -/
theorem hlastByte_zero {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : ZeroDocument G) :
    hlastByte G (walkSeed G S) = BitVec.ofNat 8 48 := by
  have hk : (walkSeed G S).k = 0 := rfl
  have hbyte : entryByte G (walkSeed G S).k = 48 := by
    rw [hk]
    exact h.entryByte_zero
  simp only [hlastByte, hbyte]
  rfl

/-- **The bundle's class bit is `1` at the document `0`.**  `48` is below `125` in the
signed order, so the pivot's `slt` is set — the bit the bundle requires to be clear. -/
theorem zeroDocument_class_false {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : ZeroDocument G) :
    evalICmp .slt (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 125) = 1 := by
  rw [hlastByte_zero G S h]
  decide

/-- **The old residue is empty at the document `0`.**  `HlastResidue`'s first field is
the bit `zeroDocument_class_false` shows to be `1`, so no last-entry bundle of the
branch-specific class exists at this adopted input. -/
theorem zeroDocument_residue_false {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : ZeroDocument G) (r : HlastResidue G (walkSeed G S) s) : False := by
  have hbit := zeroDocument_class_false G S h
  have hzero := r.hlt125
  rw [hbit] at hzero
  exact absurd hzero (by decide)

/-! ### The seed, at the record's own staging

`walkSeedInvariant_geometry` is the reachability theorem: at the documented staging (the
thirteen ABI arguments, the eight appended objects and the entry state's ten cells) the
state the entry run hands the loop satisfies `WalkInv`.  The cells are the entry state's
own, read out of `walkEntryState_env`, so nothing about them is supplied here. -/

/-- **The seeded head for the document `0` is reachable and invariant-holding.**  The
state is `walkSeedFinalState`'s — the entry run's handoff — and its invariant is the seed
theorem's at the record's args. -/
theorem zeroDocument_seededInv {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : ZeroDocument G) :
    WalkInv G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  refine walkSeedInvariant_geometry G S
    (EntryState stage2Body
      (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next) hn
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · rw [hargs, walkEntryState_env]
    simp [lookupName]
  · exact hnext.symm
  · rw [hargs, walkEntryState_env]
    simp [lookupName]

/-- **The seeded head is the and the guard holds.**  The first entry of a one-entry stream is
the last one: `0 + 1 < 1` is false. -/
theorem zeroDocument_seededGuard {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : ZeroDocument G) :
    (walkSeed G S).block = walkLoopHead ∧ ¬ ((walkSeed G S).k + 1 < G.nep) := by
  refine ⟨walkSeed_block G S, ?_⟩
  rw [h.count]
  show ¬ (0 + 1 < 1)
  omega

/-- **The old universal residue has no inhabitant at the document `0`.**  This is the
pre-change `WalkLoopEnd.hlast`'s type — a function returning `HlastResidue` at *every*
last-entry head state — read at the seeded head: the seed theorems supply the invariant,
the block and the guard, and the residue is empty there.  So the old field was false of an
admitted one-entry document, not merely strong. -/
theorem zeroDocument_oldField_uninhabited {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : ZeroDocument G)
    (hlast : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      ¬ (C.k + 1 < G.nep) → HlastResidue G C s) : False := by
  obtain ⟨hblock, hguard⟩ := zeroDocument_seededGuard G S h
  exact zeroDocument_residue_false G S _ h
    (hlast _ _ (zeroDocument_seededInv (S := S) hargs hnext h) hblock hguard)

/-- **The high-byte arm's evidence is empty at the document `0`.**  `IsEmpty` is the
machine-checkable form: there is no `HlastResidue` at the seeded head, so the old
universal `WalkLoopEnd.hlast : … → HlastResidue` had no inhabitant there. -/
theorem zeroDocument_highByteArm_empty {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : ZeroDocument G) : IsEmpty (HlastResidue G (walkSeed G S) s) :=
  ⟨fun r => zeroDocument_residue_false G S s h r⟩

/-- **The document `0`'s arm, and the seeded head that takes it.**  The head byte is
`0x30`; the head switch's default-arm pivots are `91` (true), `44` (false), `58` (true)
and `44` (not equal), and the tag test is true — the scalar arm's class, one of the arms
`LastEntryArm` carries.  The seed theorems put the state in the invariant at the loop
head with the last-entry guard. -/
theorem zeroDocument_domain {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : ZeroDocument G) :
    evalICmp .slt (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 91) = 1 ∧
      evalICmp .slt (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 44) = 0 ∧
      evalICmp .slt (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 58) = 1 ∧
      evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 44) = 0 ∧
      (evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 45) |||
        evalICmp .ult (hlastByte G (walkSeed G S) + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10)) = 1 ∧
      WalkInv G (walkSeed G S)
        (walkSeedFinalState G S
          (EntryState stage2Body
            (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
          (entryPos G 0) (entryByte G 0)) ∧
      (walkSeed G S).block = walkLoopHead ∧ ¬ ((walkSeed G S).k + 1 < G.nep) := by
  have hb := hlastByte_zero G S h
  obtain ⟨hblock, hguard⟩ := zeroDocument_seededGuard G S h
  exact ⟨by rw [hb]; decide, by rw [hb]; decide, by rw [hb]; decide, by rw [hb]; decide,
    by rw [hb]; decide, zeroDocument_seededInv (S := S) hargs hnext h, hblock, hguard⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hlastByte_zero
#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_class_false
#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_residue_false
#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_oldField_uninhabited
#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_highByteArm_empty
#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_seededInv
#print axioms LeanLLVM.Refinement.WalkScope.zeroDocument_domain

end WalkScope
end LeanLLVM.Refinement
