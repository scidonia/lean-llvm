/-
The continuing-entry bundle's domain, and the ordinary token it excludes.

`HcontCase` (`JsonStage2WalkDispatchWitnessString`) is the continuing branch's premise:
one bundle per class at every head state with an entry left.  Its two one-entry arms are
`HcontFacts` and `HcontCleanupFacts`, and both require their head byte to clear two
pivots:

```
evalICmp .slt x (ofNat 8 125) = 0
evalICmp .eq  x (ofNat 8 125) = 0
```

`icmp slt i8` is the *signed* order, so the first bit clear puts the byte at 125, 126 or
127 and the second removes 125 — the byte is 126 or 127, the two invalid UTF-8 leads and
the `NodeBlock19 → NodeBlock17 → LeafBlock15` arm of the head switch.  The second one-entry
arm, `HcontCleanupFacts`, carries the same two bits.  The third, `HstringFacts`, requires
`evalICmp .eq x (ofNat 8 34) = 1` — the string opener.

So the class split *as it stands* is not a split of the head switch: it is one switch arm
(the high two bytes), the string opener, and nothing else.  An ordinary continuing token —
a numeral at a non-last entry, byte `0x30` — is a *different* switch arm
(`NodeBlock5 → NodeBlock → LeafBlock1 → sw.default.i`, whose tag test then takes the value
path), and no arm of `HcontCase` describes it.  This module states the refutation at a real
input rather than at a hand-built state.

The document is `"01"`: two entries at positions `0` and `1`, so the head state at index
zero has one after it (`0 + 1 < 2`) and the continuing branch runs.  The *seed* theorems
establish reachability — `walkSeed_block` and `walkSeedInvariant_geometry` at the record's
own staging — and the head byte is the document's, read through `WalkGeom.doc` and
`WalkGeom.entries`, so the class bits are facts about the staged memory and not about a
term chosen here.

The shape of the result, in the order it is proved:

* `TwoEntryDocument` — the staged document `"01"` and its two entries, as the two reads
  and the two counts;
* `hcontByte_two` — the head byte at index zero is `48` (from `WalkGeom.doc`,
  `WalkGeom.entries` and `WalkGeom.inside`'s position zero);
* `twoEntryDocument_ws_empty` / `_cleanup_empty` / `_string_empty` — each arm of
  `HcontCase` is empty at the seeded head: the two one-entry arms on the byte's `slt`
  pivot, the string arm on the opener test;
* `twoEntryDocument_case_empty` — hence `HcontCase G (walkSeed G S) s` is empty there, and
  `WalkContinueFacts G` has no inhabitant whose head state is this one;
* `twoEntryDocument_scalar_domain` — the positive half: the head byte `48`'s `HeadArm`
  class is the default arm's, and the tag test there is *true*, the plain-value path.  That
  is the class the new arm carries, so the excluded token is not merely unexcluded.

The refutation is *about the input*, and it is what the continuing dispatch's census
(`JsonStage2WalkDispatchHcontArms`) replaces: the continuing entry's class is the head
switch's arm, and every arm owns its premises.
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

/-! ### The document `"01"`, as the staging hands it over -/

/-- **The two-byte document `"01"` and its two entries.**  The two reads are the staged
memory's (`WalkGeom.doc` and `WalkGeom.entries`), the two counts are the ABI's, and the
document's bytes are `0x30 0x31` — the JSON scalar `0` followed by a byte that keeps the
first entry from being the last.  `entries` says the stream holds two lanes, at positions
zero and one, so the first entry's token is the byte `0x30` and the head state at index
zero is a continuing one. -/
structure TwoEntryDocument {m0 : Mem} (G : WalkGeom m0) : Prop where
  /-- The document is two bytes long. -/
  len : G.n = 2
  /-- The entry stream holds two entries. -/
  count : G.nep = 2
  /-- The document's bytes are `0x30` and `0x31`. -/
  bytes : readBytes m0 G.b 2 = some [48, 49]
  /-- The entry stream's lanes are zero and one. -/
  lane : readLanes32 m0 G.ep 2 = some [0, 1]

/-- The document's byte list is the read's: `WalkGeom.doc` at the length `len`. -/
theorem TwoEntryDocument.bs {m0 : Mem} {G : WalkGeom m0} (h : TwoEntryDocument G) :
    G.bs = [48, 49] := by
  have hread : readBytes m0 G.b G.n = some [48, 49] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The entry stream's lanes are the read's: `WalkGeom.entries` at the count `count`. -/
theorem TwoEntryDocument.ent {m0 : Mem} {G : WalkGeom m0} (h : TwoEntryDocument G) :
    G.ent = [0, 1] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0, 1] := by rw [h.count]; exact h.lane
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The first entry's position is zero: the lane list is `[0, 1]`. -/
theorem TwoEntryDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0}
    (h : TwoEntryDocument G) : entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The document's byte at the first entry is `0x30`: the byte list is `[48, 49]`. -/
theorem TwoEntryDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0}
    (h : TwoEntryDocument G) : entryByte G 0 = 48 := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [48, 49] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- **The seeded head's byte is `48`.**  The seed's index is zero, and the byte is the
document's at the first entry's position. -/
theorem hcontByte_two {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : TwoEntryDocument G) :
    hlastByte G (walkSeed G S) = BitVec.ofNat 8 48 := by
  have hk : (walkSeed G S).k = 0 := rfl
  have hbyte : entryByte G (walkSeed G S).k = 48 := by
    rw [hk]
    exact h.entryByte_zero
  simp only [hlastByte, hbyte]
  rfl

/-- **The bundle's class bit is `1` at the document `"01"`.**  `48` is below `125` in the
signed order, so the pivot's `slt` is set — the bit the two one-entry bundles require to
be clear. -/
theorem twoEntryDocument_class_true {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : TwoEntryDocument G) :
    evalICmp .slt (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 125) = 1 := by
  rw [hcontByte_two G S h]
  decide

/-- **The string opener's test is clear at the document `"01"`.**  `48 ≠ 34`, so the
third arm's opener bit is `0` — the bit `HstringFacts` requires to be `1`. -/
theorem twoEntryDocument_opener_false {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : TwoEntryDocument G) :
    evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 34) = 0 := by
  rw [hcontByte_two G S h]
  decide

/-- **The head's byte at the seeded state is the bundle's witness.**  `WalkInv.iter.reg8`
reads `%8` as `hlastByte`, and the bundle's `h8` reads it as `x`, so the two witnesses
agree — the cell is a function of the state, not of the bundle. -/
theorem hcontWitness_eq {m0 : Mem} (G : WalkGeom m0) (_S : WalkStage G) {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) {x : BitVec 8}
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    x = hlastByte G C := by
  have hiter : evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C)) :=
    LeanLLVM.evalOperand_reg_of hInv.iter.reg8
  rw [h8] at hiter
  have h2 := Option.some.inj hiter
  simp only [Value.int.injEq] at h2
  exact eq_of_heq h2.2

/-! ### The three arms are empty at the seeded head -/

/-- **The whitespace arm has no inhabitant at the document `"01"`.**  Its first class bit
is the byte's `slt 125`, which is `1` at `48`; the bundle requires `0`. -/
theorem twoEntryDocument_ws_empty {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : TwoEntryDocument G) (hInv : WalkInv G (walkSeed G S) s) :
    ¬ Nonempty (HcontFacts G (walkSeed G S) s) := by
  rintro ⟨f⟩
  have hx : f.x = hlastByte G (walkSeed G S) :=
    hcontWitness_eq G S hInv f.h8
  have hbit := twoEntryDocument_class_true G S h
  have hzero := f.hlt125
  rw [hx, hbit] at hzero
  exact absurd hzero (by decide)

/-- **The scan-free arm has no inhabitant at the document `"01"`.**  The same first class
bit, at the same byte. -/
theorem twoEntryDocument_cleanup_empty {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : TwoEntryDocument G) (hInv : WalkInv G (walkSeed G S) s) :
    ¬ Nonempty (HcontCleanupFacts G (walkSeed G S) s) := by
  rintro ⟨f⟩
  have hx : f.x = hlastByte G (walkSeed G S) :=
    hcontWitness_eq G S hInv f.h8
  have hbit := twoEntryDocument_class_true G S h
  have hzero := f.hlt125
  rw [hx, hbit] at hzero
  exact absurd hzero (by decide)

/-- **The two-entry arm has no inhabitant at the document `"01"`.**  Its opener bit is
`eq 48 34`, which is `0`; the bundle requires `1`. -/
theorem twoEntryDocument_string_empty {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : TwoEntryDocument G) (hInv : WalkInv G (walkSeed G S) s) :
    ¬ Nonempty (HstringFacts G (walkSeed G S) s) := by
  rintro ⟨f⟩
  have hx : f.x = hlastByte G (walkSeed G S) :=
    hcontWitness_eq G S hInv f.h8
  have hbit := twoEntryDocument_opener_false G S h
  have hone := f.heq34
  rw [hx, hbit] at hone
  exact absurd hone (by decide)

/-- **The continuing class is empty at the document `"01"`.**  Every constructor of
`HcontCase` is one of the three arms, and each is empty at the seeded head: so the
continuing premise cannot describe this ordinary token at all. -/
theorem twoEntryDocument_case_empty {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : TwoEntryDocument G) (hInv : WalkInv G (walkSeed G S) s) :
    IsEmpty (HcontCase G (walkSeed G S) s) :=
  ⟨fun c => by
    cases c with
    | ws f => exact twoEntryDocument_ws_empty G S s h hInv ⟨f⟩
    | cleanup f => exact twoEntryDocument_cleanup_empty G S s h hInv ⟨f⟩
    | twoEntry f => exact twoEntryDocument_string_empty G S s h hInv ⟨f⟩⟩

/-! ### The seed, at the record's own staging

`walkSeedInvariant_geometry` is the reachability theorem: at the documented staging (the
thirteen ABI arguments, the eight appended objects and the entry state's ten cells) the
state the entry run hands the loop satisfies `WalkInv`.  The cells are the entry state's
own, read out of `walkEntryState_env`, so nothing about them is supplied here.
-/

/-- **The seeded head for the document `"01"` is reachable and invariant-holding.**  The
state is `walkSeedFinalState`'s — the entry run's handoff — and its invariant is the seed
theorem's at the record's args. -/
theorem twoEntryDocument_seededInv {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryDocument G) :
    WalkInv G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  refine walkSeedInvariant_geometry G S
    (EntryState stage2Body
      (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next) hn
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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

/-- **The seeded head is at the loop head and the continuing guard holds.**  The first of
two entries has one after it: `0 + 1 < 2`. -/
theorem twoEntryDocument_seededGuard {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : TwoEntryDocument G) :
    (walkSeed G S).block = walkLoopHead ∧ (walkSeed G S).k + 1 < G.nep := by
  refine ⟨walkSeed_block G S, ?_⟩
  rw [h.count]
  show 0 + 1 < 2
  omega

/-- **The continuing premise has no inhabitant at the document `"01"`.**  This is the
pre-change `WalkContinueFacts`'s shape — a function returning `HcontCase` at every head
state with an entry left — read at the seeded head: the seed theorems supply the invariant,
the block and the guard, and the class is empty there.  So the old split was false of an
admitted two-entry document, not merely strong. -/
theorem twoEntryDocument_oldField_uninhabited {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryDocument G)
    (hcont : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → HcontCase G C s) : False := by
  obtain ⟨hblock, hguard⟩ := twoEntryDocument_seededGuard G S h
  let s := walkSeedFinalState G S
    (EntryState stage2Body
      (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
    (entryPos G 0) (entryByte G 0)
  have hInv : WalkInv G (walkSeed G S) s :=
    twoEntryDocument_seededInv (S := S) hargs hnext h
  exact (twoEntryDocument_case_empty G S s h hInv).false
    (hcont (walkSeed G S) s hInv hblock hguard)

/-- **The positive half: the document `"01"`'s head is the scalar arm's class.**  The head
byte is `0x30`, the head switch's default-arm pivots are `91` (true), `44` (false), `58`
(true) and `44` (not equal), and the tag test at the token's end is *true* — the
plain-value path the new scalar arm takes.  The seed theorems put the state in the
invariant at the loop head with the continuing guard. -/
theorem twoEntryDocument_scalar_domain {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryDocument G) :
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
      (walkSeed G S).block = walkLoopHead ∧ (walkSeed G S).k + 1 < G.nep := by
  have hb := hcontByte_two G S h
  obtain ⟨hblock, hguard⟩ := twoEntryDocument_seededGuard G S h
  exact ⟨by rw [hb]; decide, by rw [hb]; decide, by rw [hb]; decide, by rw [hb]; decide,
    by rw [hb]; decide, twoEntryDocument_seededInv (S := S) hargs hnext h, hblock, hguard⟩

/-- **The whitespace producer's first class premise is false at the document `"01"`.**
`hcontFacts_of_staging` asks for `evalICmp .slt (hlastByte G C) 125 = 0` and
`evalICmp .eq (hlastByte G C) 125 = 0`; at this head the first reads `1`, so the producer
cannot be applied — the refutation is at its own argument, not only at the bundle it
builds.  The scan-free producer (`HcontCleanupFacts`) shares the same premise. -/
theorem twoEntryDocument_producer_premise_false {m0 : Mem} (G : WalkGeom m0)
    (S : WalkStage G) (h : TwoEntryDocument G) :
    ¬ (evalICmp .slt (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 125) = 0) := by
  intro hz
  have h1 := twoEntryDocument_class_true G S h
  rw [h1] at hz
  exact absurd hz (by decide)

/-- **The seeded head is reachable and continuing, and its class is the empty one.**  The
regression's shape in one statement: the seed's invariant and guard, the head byte `48`,
and the class type empty there. -/
theorem twoEntryDocument_regression {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryDocument G) :
    hlastByte G (walkSeed G S) = BitVec.ofNat 8 48 ∧
      WalkInv G (walkSeed G S)
        (walkSeedFinalState G S
          (EntryState stage2Body
            (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
          (entryPos G 0) (entryByte G 0)) ∧
      (walkSeed G S).block = walkLoopHead ∧ (walkSeed G S).k + 1 < G.nep ∧
      IsEmpty (HcontCase G (walkSeed G S)
        (walkSeedFinalState G S
          (EntryState stage2Body
            (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
          (entryPos G 0) (entryByte G 0))) := by
  obtain ⟨hblock, hguard⟩ := twoEntryDocument_seededGuard G S h
  exact ⟨hcontByte_two G S h,
    twoEntryDocument_seededInv (S := S) hargs hnext h, hblock, hguard,
    twoEntryDocument_case_empty G S _ h
      (twoEntryDocument_seededInv (S := S) hargs hnext h)⟩

/-- **The census names the document `"01"`'s head.**  The seeded head's byte is `0x30`, and
`0x30`'s class is `HcontClass.value` — the plain-value arm whose producer is
`walkRevolutionMergeSegScalar`.  So the excluded token is not merely unexcluded: the
continuing census gives it an arm, and that arm is the one the old split had no constructor
for. -/
theorem twoEntryDocument_class_value {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : TwoEntryDocument G) :
    HcontClass (hlastByte G (walkSeed G S)) := by
  rw [hcontByte_two G S h]
  exact HcontClass.value_of_48

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontByte_two
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_class_true
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_opener_false
#print axioms LeanLLVM.Refinement.WalkScope.hcontWitness_eq
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_ws_empty
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_cleanup_empty
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_string_empty
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_case_empty
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_seededInv
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_oldField_uninhabited
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_producer_premise_false
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_regression
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_class_value
#print axioms LeanLLVM.Refinement.WalkScope.twoEntryDocument_scalar_domain

end WalkScope
end LeanLLVM.Refinement
