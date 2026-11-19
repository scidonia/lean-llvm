/-
# The continuing payload's callee rows and its visits, from the invariant

`HcontPayload` (`JsonStage2WalkDispatchSupply`) has three groups.  `lane` is produced
(`JsonStage2WalkDispatchDefaultLane`: the default row) and `HcontLane.string` is the
standalone string's read row; this module takes the callee side:

* `HcontAbi.openCall` — **produced** (`hcontAbi_openCall`): the root slot's word
  (`walkReadBytes_rootSlot_word`), the callee's precondition (`s2ValuePosPre_of_inv`) and
  its answer (`s2ValuePos_answers`).  That is `hlastAbi_openCall`'s producer at the
  continuing head, and the field takes nothing the invariant does not carry;
* `HcontAbi.string` — **false as stated** and reported rather than repaired: its
  `hbranch` demands a nonzero value-position answer, which at depth zero the model gives
  only when the root word is `0` (`stage2ValuePos`).  The field quantifies over every
  `rd : BitVec 32` and every `A : BitVec 64`, so `HcontStringCalls` is uninhabited at
  `rd = ofNat 32 1` (`hcontStringCalls_uninhabited_of_ne`).  `hR8` is a second,
  independent row (the string body's acceptance, a `document` fact), and `hpreS`'s
  arena-presence clause is the third: the field's intended use
  (`hcontArm_twoEntry_of_payload`) asks it at the *lane's* `rd`/`A`, and the universal in
  the field's type is what makes it fail;
* `HcontTrav.visits` — **not a consequence of the geometry**, and the row it needs is
  named: `ScanVisits G c i`'s `∃` carries the visited byte's class
  (`slt x 13 = 1 ∧ ule (x + 247) 1 = 1`, the `9`/`10` arm), which is the document's
  content.  `scanVisits_of_class` proves the whole proposition from that one row; every
  other part — `%3`'s address, the read, the `%47` cell and the three local facts — is
  the invariant's.  `WalkGeom` constrains no byte value (`doc` is `readBytes m0 b n =
  some bs`), so no producer can supply the class at a variable geometry.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### `HcontAbi.openCall`, produced

The root slot's word, the callee's precondition and the call are all the invariant's:
`hcontOpenCall_of_inv` is that composition, and it does not mention the block or the
entry count.  So the field is the same producer `hlastAbi_openCall` uses, at a
continuing head. -/

/-- **`HcontAbi.openCall`, produced**: the openers' value-position call at every state
that carries the invariant.  The root slot's word is `walkReadBytes_rootSlot_word`, the
precondition is the invariant's (`WalkInv.tyBytes`/`stBytes` at `C.sp - 1`, or nothing at
depth zero), and the answer is `s2ValuePos_answers`.  Nothing is supplied.

The same composition is `hcontOpenCall_of_inv` (`JsonStage2WalkDispatchHlastSupply`);
it is written out here because that module is not in the build lane's snapshot, so this
module depends only on the payload's own modules.  Where that one is available the body
is `hcontOpenCall_of_inv hInv`. -/
noncomputable def hcontAbi_openCall {m0 : Mem} (G : WalkGeom m0) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → HcontOpenCall G C s := by
  intro C s hInv _ _
  let rdv : BitVec 32 := Classical.choose (walkReadBytes_rootSlot_word hInv)
  have hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) :=
    Classical.choose_spec (walkReadBytes_rootSlot_word hInv)
  have hpre : s2ValuePosPre [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next := by
    unfold s2ValuePosPre
    refine ⟨BitVec.ofNat 32 C.sp, rdv, C.stage.ctype, C.stage.cst, rfl, ?_⟩
    have hcap : C.sp ≤ stage2StackExtent := hInv.depth_cap
    have hto : (BitVec.ofNat 32 C.sp).toNat = C.sp :=
      walkToNat_ofNat32 (by simp only [stage2StackExtent] at hcap; omega)
    rw [hto]
    by_cases h0 : C.sp = 0
    · exact Or.inl h0
    · have hlt : C.sp - 1 < C.wlen := by have := hInv.sp_le_wlen; omega
      exact Or.inr
        ⟨⟨_, WalkStackBytes.at hInv.tyBytes hlt⟩, ⟨_, WalkStackBytes.at hInv.stBytes hlt⟩⟩
  let r : CallOutcome := Classical.choose (s2ValuePos_answers hpre)
  have hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv, .ptr C.stage.ctype, .ptr C.stage.cst]
      s.mem s.next = some r := Classical.choose_spec (s2ValuePos_answers hpre)
  exact ⟨rdv, hread, hpre, r, hcall⟩

/-! ### `HcontAbi.string`: the branch field is false at a nonzero root word

`HcontStringCalls.hxv` pins every answer's return to one word `xv`, and `hbranch` asks
that word to be nonzero.  At depth zero the callee's return is
`if rd = 0 then 1 else 0` (`stage2ValuePos`), so at `rd ≠ 0` the two fields cannot both
hold: the answer is `0`.  The field quantifies over every `rd`, so it is not merely
unproduced — it is uninhabited at the `rd` the caller picks next. -/

/-- **The value-position callee at depth zero**: the model's return is `1` only for a
zero root word. -/
theorem stage2ValuePos_zero_reply {mem : Mem} {rd : BitVec 32} {ct cs : Nat} :
    stage2ValuePos mem 0 rd.toNat ct cs = some (if rd.toNat = 0 then 1 else 0) := by
  simp [stage2ValuePos]

/-- **No `HcontStringCalls` at a nonzero root word.**  The call is `hpreV`'s and the
model answers `0`; `hxv` makes that the structure's `xv`, and `hbranch` forbids it. -/
theorem hcontStringCalls_uninhabited_of_ne {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {rd : BitVec 32} {A : BitVec 64}
    (hsp : (BitVec.ofNat 32 C.sp).toNat = 0) (hrd : rd.toNat ≠ 0) :
    ¬ Nonempty (HcontStringCalls G C s rd A) := by
  rintro ⟨c⟩
  obtain ⟨r, hr⟩ := s2ValuePos_answers c.hpreV
  -- the call's answer, at depth zero
  have hcall : r.ret = .int 32 (BitVec.ofNat 32 0) := by
    have h2 : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next =
        some ⟨.int 32 (BitVec.ofNat 32 0), s.mem, s.next⟩ := by
      rw [s2ValuePos_reply, hsp, stage2ValuePos_zero_reply, ite_eq_right hrd]
      rfl
    have h3 : r = ⟨.int 32 (BitVec.ofNat 32 0), s.mem, s.next⟩ :=
      Option.some.inj (hr.symm.trans h2)
    rw [h3]
  -- so the structure's `xv` is zero
  have hxv0 : c.xv = BitVec.ofNat 32 0 := by
    have h1 := c.hxv r hr
    rw [hcall] at h1
    simp only [Value.int.injEq, true_and] at h1
    exact (eq_of_heq h1).symm
  -- and `hbranch` cannot hold
  have hb := c.hbranch
  rw [hxv0] at hb
  have hz : evalICmp .ne (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = 0 := by decide
  rw [hz] at hb
  exact absurd hb (by decide)

/-- **The `string` field's statement is false**: at `rd = ofNat 32 1` — a word the
caller may pass — the structure has no inhabitant, so no function of the field's type
returns one there.  The row the arm actually reads is the *accepting* one
(`hcontArm_twoEntry_of_payload` passes the lane's `rd`, whose word is the root slot's). -/
theorem hcontAbi_string_field_false {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hsp : C.sp = 0) (hcap : C.sp < 2 ^ 32) :
    ¬ Nonempty (HcontStringCalls G C s (BitVec.ofNat 32 1) (BitVec.ofNat 64 0)) := by
  refine hcontStringCalls_uninhabited_of_ne ?_ ?_
  · rw [walkToNat_ofNat32 hcap]
    exact hsp
  · rw [show (BitVec.ofNat 32 1).toNat = 1 from by decide]
    decide

/-! ### `HcontTrav.visits`: the invariant's part, and the document row it needs

`ScanVisits G c i` states, at every scan state with a counter `p` in `(i, c)`, that the
visit's byte is read at `%3', the byte's number is the `%47` cell, its class is the
`9`/`10` arm, and the three local facts hold.  Everything but the class is the
invariant's: `%3` is `WalkPtrs`'s document base, the read is `WalkInv.doc_read`'s
(`walkDoc_byte`), the `%47` cell is the landing's own definition, and the local facts are
`WalkLocal` at the three blocks (`ScanCount` for the latch).  The class is the
document's content at `p + 1`, which no `WalkGeom` clause pins. -/

/-- The latch binds neither `%3`, `%q.0.i246` nor `%cond350.i`. -/
theorem scanLatchOut_env3 (s : State) (i c : Nat) (t : String) :
    lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c t).env "%3" =
      lookupName s.env "%3" := by
  simp only [stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The latch keeps `%cond350.i`. -/
theorem scanLatchOut_envCond (s : State) (i c : Nat) (t : String) :
    lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c t).env "%cond350.i" =
      lookupName s.env "%cond350.i" := by
  simp only [stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The stop's landing binds `%q.0.i246` to its own index. -/
theorem latch462S_envQ (s : State) (idx : BitVec 64) (a q : Nat) (x : BitVec 8) :
    lookupName (Latch462S s idx a q x).env "%q.0.i246" = some (.int 64 idx) := by
  simp only [landRhs457OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The latch keeps `%cond350.i`. -/
theorem latch462S_envCond (s : State) (idx : BitVec 64) (a q : Nat) (x : BitVec 8) :
    lookupName (Latch462S s idx a q x).env "%cond350.i" =
      lookupName s.env "%cond350.i" := by
  simp only [landRhs457OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **The visits, from the visited bytes' class.**  The `∃`'s other parts are the
invariant's and the landing's cells; the class is the row. -/
theorem scanVisits_of_class {m0 : Mem} (G : WalkGeom m0) {c i : Nat}
    (hc : c ≤ G.n) (hcw : c < 2 ^ 64)
    (hcls : ∀ p, i < p + 1 → p + 1 < c →
      evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    ScanVisits G c i := by
  intro K' t' p hInv' hblock hi hlt hq hcond
  -- the document's byte at the visited index
  have hq1 : p + 1 < G.n := by omega
  have hbyte : readBytes t'.mem (G.b + (p + 1)) 1 = some [G.bs.getD (p + 1) 0] :=
    walkDoc_byte G K' t' hInv' (by have h := hInv'.alen_le; omega)
      (le_trans hInv'.evlen_le G.evRoom) hq1
  -- the latch's cells
  have h3 : lookupName (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c
      "land.rhs457.i").env "%3" = some (.ptr G.b) := by
    rw [scanLatchOut_env3]
    exact hInv'.ptrs.1
  have hcondL : lookupName (Latch462S (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c
      "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) G.b (G.bs.getD (p + 1) 0).toNat
      (BitVec.ofNat 8 ((G.bs.getD (p + 1) 0).toNat))).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    rw [latch462S_envCond, scanLatchOut_envCond]
    exact hcond
  refine ⟨G.b, [G.bs.getD (p + 1) 0], (G.bs.getD (p + 1) 0).toNat,
    BitVec.ofNat 8 ((G.bs.getD (p + 1) 0).toNat), h3, hbyte, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evalOperand, landRhs457OutAt, stateAt, cells]
    rw [lookupName_cons_self]
  · simpa only [wsX, wsByte] using (hcls p hi hlt).1
  · simpa only [wsX, wsByte] using (hcls p hi hlt).2
  · -- the first landing's local fact: `NodeBlock105`'s `WalkLocal` is `True`
    simp [WalkLocal]
  · -- the first pivot's local fact: `LeafBlock96`'s
    simp [WalkLocal]
  · -- the latch's local fact: `ScanCount` at the counters the landing wrote
    have hSC : ScanCount t' "%q.0.i246" "%cond350.i" K'.inner := by
      have h := hInv'.blockLocal
      rwa [WalkLocal.extraToken hblock] at h
    have hsub : c - p ≤ K'.inner := ScanCount.same hSC hq hcond hcw (by omega)
    have hsub' : c - (p + 1) ≤ K'.inner := by omega
    have hqL₂ : lookupName (Latch462S (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) G.b (G.bs.getD (p + 1) 0).toNat
        (BitVec.ofNat 8 ((G.bs.getD (p + 1) 0).toNat))).env "%q.0.i246" =
        some (.int 64 (BitVec.ofNat 64 (p + 1))) :=
      latch462S_envQ _ _ _ _ _
    rw [WalkLocal.extraToken rfl]
    exact ⟨p + 1, c, hsub', hlt, hcw, hqL₂, hcondL⟩

/-- **`HcontTrav.visits` from the visited bytes' class.**  The row the field needs is
`hcls`: every index the extra-token scan visits reads a `9` or `10` byte, i.e.
`wsVisit_class_of_byte`'s two bits at `wsX G (p + 1)`.  `c = entryPos G (C.k + 1)` is
inside the document and below `2 ^ 64` (`entryPos_lt`, `entryPos_lt_64`), which is what
`scanVisits_of_class`'s two side conditions need. -/
theorem hcontTrav_visits_of_class {m0 : Mem} (G : WalkGeom m0)
    (hcls : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → ∀ p, entryPos G C.k < p + 1 → p + 1 < entryPos G (C.k + 1) →
      evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → ScanVisits G (entryPos G (C.k + 1)) (entryPos G C.k) :=
  fun C s hInv hblock hk =>
    scanVisits_of_class G (le_of_lt (entryPos_lt G hk)) (entryPos_lt_64 G (C.k + 1))
      (fun p h1 h2 => hcls C s hInv hblock hk p h1 h2)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontAbi_openCall
#print axioms LeanLLVM.Refinement.WalkScope.stage2ValuePos_zero_reply
#print axioms LeanLLVM.Refinement.WalkScope.hcontStringCalls_uninhabited_of_ne
#print axioms LeanLLVM.Refinement.WalkScope.hcontAbi_string_field_false
#print axioms LeanLLVM.Refinement.WalkScope.scanLatchOut_env3
#print axioms LeanLLVM.Refinement.WalkScope.scanLatchOut_envCond
#print axioms LeanLLVM.Refinement.WalkScope.latch462S_envQ
#print axioms LeanLLVM.Refinement.WalkScope.latch462S_envCond
#print axioms LeanLLVM.Refinement.WalkScope.scanVisits_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontTrav_visits_of_class

end WalkScope
end LeanLLVM.Refinement
