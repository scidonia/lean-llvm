/-
`if.end133.i`'s target, named: the composite of the block's link and its step.

`WalkLink.if_end133_i` gives the link and an existential target; `pairStep` gives the
same source's step at the environment the run names.  `Ctrl.jump`'s injectivity
identifies the two, so the arm has the block's target as a term.

The two peels are the cells the comma's later blocks read: `%22` (the state stack's
byte, which selects the marker's branch) and `%arrayidx143.i` (its address, which the
merge's store writes through).  Both are record projections on the literal cell list,
so they reduce; a `simp` over `walkPairEnv` does not, and is not used.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchDepthStates

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **`if.end133.i`, its target named.** -/
theorem WalkLink.if_end133_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end133.i")
    {sp ct cs : Nat} {b b2 : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread1 : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b])
    (hread2 : readBytes s.mem
      (cs + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b2]) :
    ∃ s', WalkLink calls G C s { C with block := (if pairBit (BitVec.ofNat 8 b.toNat) = 1
        then "if.then141.i" else "if.else153.i") } s' ∧
      s' = pairNext s sp ct cs b b2 := by
  obtain ⟨s', hl⟩ := WalkLink.if_end133_i (calls := calls) G C s hInv hblock hsp hct hcs
    hq63 hread1 hread2
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump (pairNext s sp ct cs b b2) :=
    pairStep (calls := calls) (G := G) (C := C) (s := s) (hInv := hInv)
      (B := walkIf_end133_i) (by rw [hblock]; exact walkIf_end133_i_find) rfl rfl
      (env' := pairEnv s sp ct cs b b2) rfl hsp hct hcs
      (gg := "%sub135.i") (zx := "%idxprom136.i") (ap1 := "%arrayidx137.i")
      (ld1 := "%21") (d := "%cmp139.i") (ap2 := "%arrayidx143.i") (ld2 := "%22")
      (base1 := "%ctype.i") (base2 := "%cst.i") (tl := "if.then141.i")
      (fl := "if.else153.i") (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 4294967295)
      (a1 := ct) (a2 := cs) (one := BitVec.ofNat 8 1) (bs := [b]) (bs2 := [b2])
      (q := b.toNat)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hq63 (bytesToNat_singleton b) hread1 hread2
  exact ⟨s', hl, Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)⟩

/-- The pair's `%22` cell: the state stack's byte. -/
theorem pairOut_22 (s : State) (sp ct cs : Nat) (b b2 : UInt8) :
    lookupName (pairOut s sp ct cs b b2).env "%22" =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
  have h : lookupName (pairOut s sp ct cs b b2).env "%22" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat [b2]))) := rfl
  rw [h, bytesToNat_singleton]

/-- The pair's `%arrayidx143.i` cell: the state stack's byte address. -/
theorem pairOut_ap2 (s : State) (sp ct cs : Nat) (b b2 : UInt8) :
    lookupName (pairOut s sp ct cs b b2).env "%arrayidx143.i" =
      some (.ptr (cs + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat)) := by
  dsimp only [pairOut, pairEnv, stateAt, walkPairEnv, cells]
  rw [lookupName_cons_ne (k := "%22") (n := "%arrayidx143.i") _ _ (by decide)]
  rfl

/-- The pair's offset is the depth less one, for a positive depth. -/
theorem pairOff_eq {sp : Nat} (hpos : 0 < sp) (hsp32 : sp < 2 ^ 32) :
    (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat = sp - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hb : (4294967295 : Nat) < 2 ^ 32 := by decide
  rw [Nat.mod_eq_of_lt hsp32, Nat.mod_eq_of_lt hb]
  rw [show sp + 4294967295 = (sp - 1) + 4294967296 from by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- The pair's branch bit at a brace's marker. -/
theorem pairBit_one : pairBit (BitVec.ofNat 8 1) = 1 := by decide

/-- The pair's branch bit at a non-brace byte. -/
theorem pairBit_zero {b : BitVec 8} (h : b ≠ BitVec.ofNat 8 1) : pairBit b = 0 :=
  refuseICmp_eq_zero h

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end133_at

end WalkScope
end LeanLLVM.Refinement
