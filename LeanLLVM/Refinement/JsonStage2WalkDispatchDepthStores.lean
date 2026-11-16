/-
The merge's state-stack stores and the colon's marker test, at named targets.

`if.end150.i`, `if.end162.i` and `if.end195.i` write one literal byte at the state
stack's index and jump to the merge.  `WalkLink.store8Stack` proves the link with an
existential target, while the merge's `pre` and its `phi` cells are read at that
target, so the arms compose at a name: `stackStoreOut` is the written memory at the
source's environment, and `stackStoreStep` is the block's own step there.

`lor.lhs.false.i` is the colon's state-stack marker test: it reads the byte at the
index `if.end179.i` left and branches on it.  `lorOut` names its three cells.
-/
import LeanLLVM.Refinement.JsonStage2WalkPure
import LeanLLVM.Refinement.JsonStage2WalkStore

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The three state-stack stores -/

/-- The store's run state: the source's environment at the written memory. -/
def stackStoreOut {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (x : BitVec 8) (q : Nat)
    (s : State) : State :=
  { s with
    mem := writeBytes s.mem (C.stage.cst + q) (natToBytes x.toNat 1),
    pc := "cleanup478.i",
    pre := some s.pc }

/-- **The state-stack store's step, at the named target.** -/
theorem stackStoreStep {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {p : String} {x : BitVec 8} {q : Nat}
    (hinstrs : B.instrs = [Instr.store (.int 8) (.imm (.int 8 x)) (.reg p)])
    (hterm : B.term = Term.br "cleanup478.i")
    (hp : lookupName s.env p = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    LeanLLVM.step calls stage2Body s = Ctrl.jump (stackStoreOut C x q s) := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let m' : Mem := writeBytes s.mem (C.stage.cst + q) (natToBytes x.toNat 1)
  have hden : denoteCode calls B.instrs s = some (stateAt s.env { s with mem := m' }) := by
    rw [hinstrs, ← stateAt_self s]
    exact denoteCode_store8_imm calls s.env s x p hp []
  simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
  dsimp only [stackStoreOut, m', stateAt]
  rw [hpc]

/-- **`if.end150.i`, its target named** — the state stack's byte set to `4`. -/
theorem WalkLink.if_end150_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end150.i")
    {q : Nat} (hp : lookupName s.env "%arrayidx143.i" = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with
        block := "cleanup478.i",
        stMap := fun i => if i = q then
          (natToBytes (BitVec.ofNat 8 4).toNat 1).getD 0 0 else C.stMap i } s' ∧
      s' = stackStoreOut C (BitVec.ofNat 8 4) q s := by
  obtain ⟨s', hl⟩ := WalkLink.store8Stack G C s hInv
    (by rw [hblock]; exact walkIf_end150_i_find) rfl rfl hp hq
  exact ⟨s', hl, Ctrl.jump.inj ((WalkLink.step hl).symm.trans
    (stackStoreStep G C s hInv (by rw [hblock]; exact walkIf_end150_i_find) rfl rfl hp hq))⟩

/-- **`if.end162.i`, its target named** — the state stack's byte set to `2`. -/
theorem WalkLink.if_end162_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end162.i")
    {q : Nat} (hp : lookupName s.env "%arrayidx143.i" = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with
        block := "cleanup478.i",
        stMap := fun i => if i = q then
          (natToBytes (BitVec.ofNat 8 2).toNat 1).getD 0 0 else C.stMap i } s' ∧
      s' = stackStoreOut C (BitVec.ofNat 8 2) q s := by
  obtain ⟨s', hl⟩ := WalkLink.store8Stack G C s hInv
    (by rw [hblock]; exact walkIf_end162_i_find) rfl rfl hp hq
  exact ⟨s', hl, Ctrl.jump.inj ((WalkLink.step hl).symm.trans
    (stackStoreStep G C s hInv (by rw [hblock]; exact walkIf_end162_i_find) rfl rfl hp hq))⟩

/-- **`if.end195.i`, its target named** — the state stack's byte set to `2`. -/
theorem WalkLink.if_end195_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end195.i")
    {q : Nat} (hp : lookupName s.env "%arrayidx188.i" = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with
        block := "cleanup478.i",
        stMap := fun i => if i = q then
          (natToBytes (BitVec.ofNat 8 2).toNat 1).getD 0 0 else C.stMap i } s' ∧
      s' = stackStoreOut C (BitVec.ofNat 8 2) q s := by
  obtain ⟨s', hl⟩ := WalkLink.store8Stack G C s hInv
    (by rw [hblock]; exact walkIf_end195_i_find) rfl rfl hp hq
  exact ⟨s', hl, Ctrl.jump.inj ((WalkLink.step hl).symm.trans
    (stackStoreStep G C s hInv (by rw [hblock]; exact walkIf_end195_i_find) rfl rfl hp hq))⟩

/-- A store's successor has the source's `%sp.i.0248`. -/
theorem stackStoreOut_depth {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (x : BitVec 8)
    (q : Nat) (s : State) {sp : Nat}
    (h : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp))) :
    lookupName (stackStoreOut C x q s).env "%sp.i.0248" =
      some (.int 32 (BitVec.ofNat 32 sp)) := h

/-- A store's successor has the source's `%inc.i`. -/
theorem stackStoreOut_inc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (x : BitVec 8)
    (q : Nat) (s : State) {k : Nat}
    (h : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 k))) :
    lookupName (stackStoreOut C x q s).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 k)) := h

/-- A store's successor's `pre` is the block's own `pc`. -/
theorem stackStoreOut_pre {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (x : BitVec 8)
    (q : Nat) (s : State) : (stackStoreOut C x q s).pre = some s.pc := rfl

/-! ### `lor.lhs.false.i`: the state stack's marker at `%sp - 1` -/

/-- `lor.lhs.false.i`'s run state: the three cells its run binds. -/
def lorOut (s : State) (cs q : Nat) (b : UInt8) : State :=
  stateAt (cells [("%cmp190.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat)
      (BitVec.ofNat 8 1))),
    ("%24", .int 8 (BitVec.ofNat 8 b.toNat)),
    ("%arrayidx188.i", .ptr (cs + q))] s.env) s

/-- `lor.lhs.false.i`'s target, at its branch bit. -/
abbrev lorNext (s : State) (cs q : Nat) (b : UInt8) : State :=
  { lorOut s cs q b with
    pc := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
      then "if.end195.i" else "if.then192.i"),
    pre := some s.pc }

/-- **`lor.lhs.false.i`'s step, at the named target.** -/
theorem lorStep {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "lor.lhs.false.i")
    {cs q : Nat} {b : UInt8}
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hidx : lookupName s.env "%idxprom182.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (cs + q) 1 = some [b]) :
    LeanLLVM.step calls stage2Body s = Ctrl.jump (lorNext s cs q b) := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfind : stage2Body.findBlock C.block = some walkLor_lhs_false_i := by
    rw [hblock]; exact walkLor_lhs_false_i_find
  have hden : denoteCode calls walkLor_lhs_false_i.instrs s = some (lorOut s cs q b) := by
    simp only [lorOut]
    rw [show walkLor_lhs_false_i.instrs = [
      Instr.gep "%arrayidx188.i" (.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom182.i"),
      Instr.load "%24" (.int 8) (Operand.reg "%arrayidx188.i"),
      Instr.icmp "%cmp190.not.i" IPred.eq 8 (Operand.reg "%24")
        (Operand.imm (.int 8 (BitVec.ofNat 8 1)))] from rfl, ← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx188.i")
      (base := "%cst.i") (off := "%idxprom182.i") (a := cs) (idx := BitVec.ofNat 64 q)
      hcs hidx (by rw [sExt_ofNat64 hq63]; exact hq63)]
    rw [sExt_ofNat64 hq63]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx188.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%24") (p := "%arrayidx188.i") (a := cs + q) (by simp [lookupName]) hread]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%24", .int 8 (BitVec.ofNat 8 b.toNat)) ::
        ("%arrayidx188.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%cmp190.not.i") (a := "%24") 8 (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 1) (by simp [lookupName])]
    rfl
  have hbit : lookupName (lorOut s cs q b).env "%cmp190.not.i" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1))) := by
    simp only [lorOut, stateAt, cells]
    rw [lookupName_cons_self]
  have hterm : walkLor_lhs_false_i.term = Term.condbr (.reg "%cmp190.not.i")
      "if.end195.i" "if.then192.i" := rfl
  simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
  rw [walkExecTerm_condbr (d := "%cmp190.not.i") (tl := "if.end195.i")
    (fl := "if.then192.i")
    (bit := evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1)) hbit]
  rfl

/-- **`lor.lhs.false.i`, its target named.** -/
theorem WalkLink.lor_lhs_false_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "lor.lhs.false.i")
    {cs q : Nat} {b : UInt8}
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hidx : lookupName s.env "%idxprom182.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (cs + q) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block :=
        (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
          then "if.end195.i" else "if.then192.i") } s' ∧
      s' = lorNext s cs q b := by
  obtain ⟨s', hl⟩ := WalkLink.lor_lhs_false_i (calls := calls) G C s hInv hblock hcs hidx
    hq63 hread
  exact ⟨s', hl, Ctrl.jump.inj ((WalkLink.step hl).symm.trans
    (lorStep G C s hInv hblock hcs hidx hq63 hread))⟩

/-- The marker's `%idxprom182.i` survives its own run as the index it read. -/
theorem lorOut_idx (s : State) (cs q : Nat) (b : UInt8) :
    lookupName (lorOut s cs q b).env "%idxprom182.i" =
      lookupName s.env "%idxprom182.i" := by
  simp only [lorOut, stateAt, cells,
    lookupName_cons_ne (k := "%cmp190.not.i") (n := "%idxprom182.i") _ _ (by decide),
    lookupName_cons_ne (k := "%24") (n := "%idxprom182.i") _ _ (by decide),
    lookupName_cons_ne (k := "%arrayidx188.i") (n := "%idxprom182.i") _ _ (by decide)]

/-- The marker's `%cst.i` survives its own run. -/
theorem lorOut_cst (s : State) (cs q : Nat) (b : UInt8) :
    lookupName (lorOut s cs q b).env "%cst.i" = lookupName s.env "%cst.i" := by
  simp only [lorOut, stateAt, cells,
    lookupName_cons_ne (k := "%cmp190.not.i") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%24") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%arrayidx188.i") (n := "%cst.i") _ _ (by decide)]

/-- The marker's `%24` cell is the state stack's byte. -/
theorem lorOut_24 (s : State) (cs q : Nat) (b : UInt8) :
    lookupName (lorOut s cs q b).env "%24" =
      some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
  simp only [lorOut, stateAt, cells]
  rw [lookupName_cons_ne (k := "%cmp190.not.i") (n := "%24") _ _ (by decide),
    lookupName_cons_self]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.stackStoreStep
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end150_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end162_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end195_at
#print axioms LeanLLVM.Refinement.WalkScope.lorStep
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.lor_lhs_false_at

end WalkScope
end LeanLLVM.Refinement
