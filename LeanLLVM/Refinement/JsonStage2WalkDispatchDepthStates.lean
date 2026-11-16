/-
The comma's container-pair state, named.

`WalkLink.if_end133_i` runs the seven-instruction pair that reads the type stack's and
the state stack's byte at `%sp - 1` and branches on the first.  The link states its
target existentially, while the block after it (`if.then141.i`) reads `%22` at that
target, so the arm composes at a *name*.

`pairEnv`/`pairOut` are the seven cells and the state they leave, and `pairStep` is
the block's own step at that state — stated generically over the environment, exactly
as `WalkLink.stackPairBr` states its run, so the term mentions the cells once.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessState

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The seven cells `if.end133.i`'s run binds, in the order it binds them. -/
abbrev pairEnv (s : State) (sp ct cs : Nat) (b b2 : UInt8) : Env :=
  walkPairEnv "%sub135.i" "%idxprom136.i" "%arrayidx137.i" "%21" "%cmp139.i"
    "%arrayidx143.i" "%22" (BitVec.ofNat 32 sp) (BitVec.ofNat 32 4294967295) ct cs
    (BitVec.ofNat 8 1) b.toNat [b2] s.env

/-- **`if.end133.i`'s run state**: the seven cells at the source's memory. -/
def pairOut (s : State) (sp ct cs : Nat) (b b2 : UInt8) : State :=
  stateAt (pairEnv s sp ct cs b b2) s

/-- **The pair's branch bit**: the type stack's byte is the brace's marker. -/
abbrev pairBit (b : BitVec 8) : BitVec 1 :=
  evalICmp .eq b (BitVec.ofNat 8 1)

/-- `if.end133.i`'s target, at the pair's branch bit. -/
abbrev pairNext (s : State) (sp ct cs : Nat) (b b2 : UInt8) : State :=
  { pairOut s sp ct cs b b2 with
    pc := (if pairBit (BitVec.ofNat 8 b.toNat) = 1 then "if.then141.i"
      else "if.else153.i"),
    pre := some s.pc }

/-- **A pair run's step, at the environment it names.**  The seven-instruction shape
`if.end133.i` and `WalkLink.stackPairBr` share: two stack bytes at `%sp + c`, the first
tested for a marker, and the branch its bit names. -/
theorem pairStep {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {gg zx ap1 ld1 d ap2 ld2 base1 base2 tl fl : String}
    {x c : BitVec 32} {a1 a2 : Nat} {one : BitVec 8} {bs : List UInt8} {bs2 : List UInt8}
    {q : Nat} {env' : Env}
    (hinstrs : B.instrs = [
      Instr.binop gg BinOp.add 32 (.reg "%sp.i.0248") (.imm (.int 32 c)),
      Instr.zext zx 32 64 (.reg gg),
      Instr.gep ap1 (.int 8) (.reg base1) (.reg zx),
      Instr.load ld1 (.int 8) (.reg ap1),
      Instr.icmp d IPred.eq 8 (.reg ld1) (.imm (.int 8 one)),
      Instr.gep ap2 (.int 8) (.reg base2) (.reg zx),
      Instr.load ld2 (.int 8) (.reg ap2)])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (henv : env' = walkPairEnv gg zx ap1 ld1 d ap2 ld2 x c a1 a2 one q bs2 s.env)
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 x))
    (hb1 : lookupName s.env base1 = some (.ptr a1))
    (hb2 : lookupName s.env base2 = some (.ptr a2))
    (hzb1 : zx ≠ base1) (hgb1 : gg ≠ base1)
    (hzb2 : zx ≠ base2) (hgb2 : gg ≠ base2)
    (hdzx : d ≠ zx) (hlzx : ld1 ≠ zx) (hazx : ap1 ≠ zx)
    (hlb2 : ld1 ≠ base2) (hab2 : ap1 ≠ base2) (hdb2 : d ≠ base2)
    (hld2d : ld2 ≠ d) (hap2d : ap2 ≠ d)
    (hpos : (x + c).toNat < 2 ^ 63)
    (hbs : bytesToNat bs = q)
    (hread1 : readBytes s.mem (a1 + (x + c).toNat) 1 = some bs)
    (hread2 : readBytes s.mem (a2 + (x + c).toNat) 1 = some bs2) :
    LeanLLVM.step calls stage2Body s =
      Ctrl.jump { stateAt env' s with
        pc := (if evalICmp .eq (BitVec.ofNat 8 q) one = 1 then tl else fl),
        pre := some s.pc } := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hden : denoteCode calls B.instrs s = some (stateAt env' s) := by
    rw [hinstrs, ← stateAt_self s]
    rw [walkDenoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := gg)
      (a := "%sp.i.0248") (w := 32) (x := x) (c := c) hsp]
    rw [denoteCode_zext (calls := calls) (env := (gg, .int 32 (x + c)) :: s.env) (s := s)
      (d := zx) (v := gg) (wIn := 32) (wOut := 64) (x := x + c) (by simp [lookupName])]
    rw [denoteCode_gep8_ofNat (calls := calls)
      (env := (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ap1) (base := base1) (off := zx) (a := a1) (j := (x + c).toNat)
      (by rw [lookupName_cons_ne (k := zx) (n := base1) _ _ hzb1,
              lookupName_cons_ne (k := gg) (n := base1) _ _ hgb1]; exact hb1)
      (by simp [lookupName]) hpos]
    rw [denoteCode_load8 (calls := calls)
      (env := (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ld1) (p := ap1) (a := a1 + (x + c).toNat) (q := q) (bs := bs)
      (by simp [lookupName]) hread1 hbs]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := (ld1, .int 8 (BitVec.ofNat 8 q)) :: (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := d) (a := ld1) (w := 8) (x := BitVec.ofNat 8 q) (c := one)
      (by simp [lookupName])]
    rw [denoteCode_gep8_ofNat (calls := calls)
      (env := (d, .int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)) ::
        (ld1, .int 8 (BitVec.ofNat 8 q)) :: (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ap2) (base := base2) (off := zx) (a := a2) (j := (x + c).toNat)
      (by
        rw [lookupName_cons_ne (k := d) (n := base2) _ _ hdb2,
            lookupName_cons_ne (k := ld1) (n := base2) _ _ hlb2,
            lookupName_cons_ne (k := ap1) (n := base2) _ _ hab2,
            lookupName_cons_ne (k := zx) (n := base2) _ _ hzb2,
            lookupName_cons_ne (k := gg) (n := base2) _ _ hgb2]
        exact hb2)
      (by
        rw [lookupName_cons_ne (k := d) (n := zx) _ _ hdzx,
            lookupName_cons_ne (k := ld1) (n := zx) _ _ hlzx,
            lookupName_cons_ne (k := ap1) (n := zx) _ _ hazx]
        simp [lookupName]) hpos]
    rw [denoteCode_load8 (calls := calls)
      (env := (ap2, .ptr (a2 + (x + c).toNat)) ::
        (d, .int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)) ::
        (ld1, .int 8 (BitVec.ofNat 8 q)) :: (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ld2) (p := ap2) (a := a2 + (x + c).toNat) (q := bytesToNat bs2)
      (bs := bs2) (by simp [lookupName]) hread2 rfl]
    rw [henv]
    rfl
  have hbit : lookupName (stateAt env' s).env d =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)) := by
    rw [henv]
    simp only [stateAt, walkPairEnv, cells]
    rw [lookupName_cons_ne (k := ld2) (n := d) _ _ hld2d,
      lookupName_cons_ne (k := ap2) (n := d) _ _ hap2d, lookupName_cons_self]
  simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
  rw [walkExecTerm_condbr (d := d) (tl := tl) (fl := fl)
    (bit := evalICmp .eq (BitVec.ofNat 8 q) one) hbit]
  dsimp only [stateAt]
  rw [hpc]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.pairStep

end WalkScope
end LeanLLVM.Refinement
