/-
The refusal arms' domain, at documents that take them.

`LastEntryArm.commaZero`/`.colonZero` and `HcontArm.commaZero`/`.colonZero` are the
comma and the colon at depth zero: the head switch selects `if.then127.i`/`if.then173.i`,
the depth register is `0`, and the run stores the entry's position at `%e + 8` and reaches
the refusal copy.  This module exhibits each arm at a **document**, so the classification
is inhabited at an input rather than only shaped:

| arm | document | head byte | entries | level |
|---|---|---|---|---|
| `commaZero` | `,` | `44` | one | last entry |
| `colonZero` | `:` | `58` | one | last entry |
| `commaZero` | `,0` | `44` | two | continuing |
| `colonZero` | `:0` | `58` | two | continuing |

The byte is read off the staged document (`WalkGeom.doc`, `WalkGeom.entries`,
`entryByte`/`entryPos`), and the state is the seed's own handoff
(`walkSeedInvariant_geometry`), so each arm's premises are facts about the input: the
head byte is the document's, the depth is the seed's, the position is the entry stream's,
and `%e` is the static carrier's.  The dispatch theorem then runs the arm, which is what
the regressions below state.

The one-entry documents are the last entry's level: `¬ (0 + 1 < 1)`.  The two-entry ones
have an entry left, which is the continuing level's guard; the *second* byte is not the
arm's and is chosen as `0` (a byte the head switch sends to the default arm, so the
document is a comma-then-scalar one, not a comma-comma one).

The negative control beside each is `zeroByte_not_comma`'s: the document `0` is the arm's
*complement* at the byte test — `48 ≠ 44` and `48 ≠ 58` — so the same detector finds the
arm absent where the byte is a digit.  That is what makes the presence a claim about the
byte rather than about the document being one long.
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

/-! ### The documents, as the staging hands them over -/

/-- **A one-byte document whose only byte is `c`.**  The two reads are the staged
memory's, the two counts are the ABI's, and the entry stream's single lane is zero, so
the entry sits at the document's first byte. -/
structure OneByteDocument {m0 : Mem} (G : WalkGeom m0) (c : UInt8) : Prop where
  /-- The document is one byte long. -/
  len : G.n = 1
  /-- The entry stream holds one entry. -/
  count : G.nep = 1
  /-- The document's byte is `c`. -/
  bytes : readBytes m0 G.b 1 = some [c]
  /-- The entry stream's lane is zero. -/
  lane : readLanes32 m0 G.ep 1 = some [0]

/-- **A two-entry document whose first byte is `c`**, the second a digit.  The lanes are
`0` and `1`, so the first entry is the document's first byte and the stream has an entry
left after it — the continuing level's guard. -/
structure TwoEntryHeadDocument {m0 : Mem} (G : WalkGeom m0) (c : UInt8) : Prop where
  /-- The document is two bytes long. -/
  len : G.n = 2
  /-- The entry stream holds two entries. -/
  count : G.nep = 2
  /-- The document's first byte is `c`; the second is a digit, which the head switch
  sends to its default arm. -/
  bytes : readBytes m0 G.b 2 = some [c, 48]
  /-- The entry stream's lanes are `0` and `1`. -/
  lanes : readLanes32 m0 G.ep 2 = some [0, 1]

/-- The one-byte document's byte list is the read's, at `len`. -/
theorem OneByteDocument.bs {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : OneByteDocument G c) : G.bs = [c] := by
  have hread : readBytes m0 G.b G.n = some [c] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The one-byte document's lanes are the read's, at `count`. -/
theorem OneByteDocument.ent {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : OneByteDocument G c) : G.ent = [0] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0] := by rw [h.count]; exact h.lane
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The one-byte document's entry is at position zero. -/
theorem OneByteDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : OneByteDocument G c) : entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The one-byte document's byte at the entry is `c`. -/
theorem OneByteDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : OneByteDocument G c) : entryByte G 0 = c := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [c] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- The two-entry document's byte list is the read's. -/
theorem TwoEntryHeadDocument.bs {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TwoEntryHeadDocument G c) : G.bs = [c, 48] := by
  have hread : readBytes m0 G.b G.n = some [c, 48] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The two-entry document's lanes are the read's. -/
theorem TwoEntryHeadDocument.ent {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TwoEntryHeadDocument G c) : G.ent = [0, 1] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0, 1] := by rw [h.count]; exact h.lanes
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The two-entry document's first entry is at position zero. -/
theorem TwoEntryHeadDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TwoEntryHeadDocument G c) : entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The two-entry document's first byte is `c`. -/
theorem TwoEntryHeadDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0} {c : UInt8}
    (h : TwoEntryHeadDocument G c) : entryByte G 0 = c := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [c, 48] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-! ### The seed, at each document

`walkSeedInvariant_geometry` is the reachability theorem: at the documented staging the
state the entry run hands the loop satisfies `WalkInv`.  The cells it asks for are the
entry state's own, read out of `walkEntryState_env`, so nothing about them is supplied
here. -/

/-- **The seeded head is reachable and invariant-holding.**  The state is
`walkSeedFinalState`'s — the entry run's handoff — and its invariant is the seed
theorem's at the record's args. -/
theorem seededInv {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (hn : 0 < G.nep) :
    WalkInv G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
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

/-! ### The head byte, the depth, the position and `%e`

The four premises the refusal arms take, read off the seeded head's invariant: the byte is
the document's (`WalkIter.reg8`), the index word is the entry stream's (`WalkInv.idx_reg`),
the depth is the seed's (`walkSeed`'s own `sp`), and `%e` is the static carrier's
(`WalkInv.regs`). -/

/-- **The seeded head's `%8` is the document's byte at the carried index.**  `WalkIter`'s
clause, whose index is the seed's zero. -/
theorem seed_reg8 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State) {c : UInt8}
    (h : OneByteDocument G c) (hInv : WalkInv G (walkSeed G S) s) :
    lookupName s.env "%8" = some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
  have h0 : entryByte G (walkSeed G S).k = c := by
    have hk : (walkSeed G S).k = 0 := rfl
    rw [hk]
    exact h.entryByte_zero
  have hiter := hInv.iter.reg8
  rw [h0] at hiter
  exact hiter

/-- **The seeded head's `%8` is the document's byte**, in the two-entry form. -/
theorem seed_reg8_two {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State) {c : UInt8}
    (h : TwoEntryHeadDocument G c) (hInv : WalkInv G (walkSeed G S) s) :
    lookupName s.env "%8" = some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
  have h0 : entryByte G (walkSeed G S).k = c := by
    have hk : (walkSeed G S).k = 0 := rfl
    rw [hk]
    exact h.entryByte_zero
  have hiter := hInv.iter.reg8
  rw [h0] at hiter
  exact hiter

/-- **The seeded head's `%idxprom.i` is the first entry's position, zero.** -/
theorem seed_idx {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (hInv : WalkInv G (walkSeed G S) s) (hpos : entryPos G 0 = 0) :
    evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 0)) := by
  have h := hInv.idx_reg
  have hk : (walkSeed G S).k = 0 := rfl
  rw [hk] at h
  rw [hpos] at h
  exact h

/-- **The seeded head's `%e` is the refusal record's address.** -/
theorem seed_e {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (hInv : WalkInv G (walkSeed G S) s) :
    lookupName s.env "%e" = some (.ptr S.e) :=
  hInv.regs ("%e", .ptr (walkSeed G S).stage.e) (by simp [walkStaticRegs])

/-! ### The four regressions

Each is the arm's evidence at its document, and the dispatch's result from it.  The
byte's class is `zeroDocument_class_false`'s complement: `48` is a digit, so the arm's
byte test is clear there — the negative control below. -/

/-- **The one-byte document `,` takes the last entry's comma-refusal arm.** -/
def commaZero_last_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (44 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)) := by
    have hreg := seed_reg8 G S s h hInv
    have htoNat : ((44 : UInt8)).toNat = 44 := by decide
    rw [htoNat] at hreg
    exact hreg
  refine .commaZero (j := 0) h8 rfl (seed_idx G S s hInv h.entryPos_zero) (seed_e G S s hInv) ?_ ?_
  · rw [h.len]
    omega
  · decide

/-- **The one-byte document `:` takes the last entry's colon-refusal arm.** -/
def colonZero_last_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (58 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)) := by
    have hreg := seed_reg8 G S s h hInv
    have htoNat : ((58 : UInt8)).toNat = 58 := by decide
    rw [htoNat] at hreg
    exact hreg
  refine .colonZero (j := 0) h8 rfl (seed_idx G S s hInv h.entryPos_zero) (seed_e G S s hInv) ?_ ?_
  · rw [h.len]
    omega
  · decide

/-- **The two-entry document `,0` takes the continuing entry's comma-refusal arm.** -/
def commaZero_cont_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (44 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)) := by
    have hreg := seed_reg8_two G S s h hInv
    have htoNat : ((44 : UInt8)).toNat = 44 := by decide
    rw [htoNat] at hreg
    exact hreg
  refine .commaZero (j := 0) h8 rfl (seed_idx G S s hInv h.entryPos_zero) (seed_e G S s hInv) ?_ ?_
  · rw [h.len]
    omega
  · decide

/-- **The two-entry document `:0` takes the continuing entry's colon-refusal arm.** -/
def colonZero_cont_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (58 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)) := by
    have hreg := seed_reg8_two G S s h hInv
    have htoNat : ((58 : UInt8)).toNat = 58 := by decide
    rw [htoNat] at hreg
    exact hreg
  refine .colonZero (j := 0) h8 rfl (seed_idx G S s hInv h.entryPos_zero) (seed_e G S s hInv) ?_ ?_
  · rw [h.len]
    omega
  · decide

/-- **The dispatch, from the last entry's comma arm.**  The arm's own evidence carries the
refusal's five fields, so `LastEntryArm.dispatch` returns the `refuse` alternative at the
seeded head — the byte `44`'s outcome, read off the dispatch rather than off the switch. -/
theorem commaZero_last_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (44 : UInt8)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hnot : ¬ ((walkSeed G S).k + 1 < G.nep) := by
    rw [h.count]
    show ¬ (0 + 1 < 1)
    omega
  exact LastEntryArm.dispatch
    (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hnot
    (commaZero_last_arm G S _ h (seededInv (S := S) hargs hnext hn))

/-- **The dispatch, from the last entry's colon arm.** -/
theorem colonZero_last_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (58 : UInt8)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hnot : ¬ ((walkSeed G S).k + 1 < G.nep) := by
    rw [h.count]
    show ¬ (0 + 1 < 1)
    omega
  exact LastEntryArm.dispatch
    (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hnot
    (colonZero_last_arm G S _ h (seededInv (S := S) hargs hnext hn))

/-- **The dispatch, from the continuing entry's comma arm.**  The continuing level's
guard is the two-entry document's `0 + 1 < 2`. -/
theorem commaZero_cont_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (44 : UInt8)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hk : (walkSeed G S).k + 1 < G.nep := by
    rw [h.count]
    show 0 + 1 < 2
    omega
  exact HcontArm.dispatch
    (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hk
    (commaZero_cont_arm G S _ h (seededInv (S := S) hargs hnext hn))

/-- **The dispatch, from the continuing entry's colon arm.** -/
theorem colonZero_cont_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (58 : UInt8)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (walkSeedFinalState G S
        (EntryState stage2Body
          (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
        (entryPos G 0) (entryByte G 0)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hk : (walkSeed G S).k + 1 < G.nep := by
    rw [h.count]
    show 0 + 1 < 2
    omega
  exact HcontArm.dispatch
    (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hk
    (colonZero_cont_arm G S _ h (seededInv (S := S) hargs hnext hn))

/-! ### The negative control

The same detector at a byte that is *not* the arm's: the document `0`'s byte is `48`, so
neither comma-refusal arm's byte test holds there.  This is what makes the presence above a
claim about the byte, not about the document being one long. -/

/-- **`48` is neither the comma nor the colon.**  The two bytes the arms test, against the
digit the document `0` carries. -/
theorem digitByte_not_comma_colon :
    evalICmp .eq (BitVec.ofNat 8 48) (BitVec.ofNat 8 44) = 0 ∧
      evalICmp .eq (BitVec.ofNat 8 48) (BitVec.ofNat 8 58) = 0 := by
  constructor <;> decide

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.commaZero_last_arm
#print axioms LeanLLVM.Refinement.WalkScope.colonZero_last_arm
#print axioms LeanLLVM.Refinement.WalkScope.commaZero_cont_arm
#print axioms LeanLLVM.Refinement.WalkScope.colonZero_cont_arm
#print axioms LeanLLVM.Refinement.WalkScope.commaZero_last_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.colonZero_last_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.commaZero_cont_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.colonZero_cont_dispatch

end WalkScope
end LeanLLVM.Refinement
