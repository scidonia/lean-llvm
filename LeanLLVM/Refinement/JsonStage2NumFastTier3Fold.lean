/-
Tier 3's starting approximation: the blocks that produce `top` and `e10`, and the
two-step error of the fold.

`to_double` reaches its emitted double through the inlined ladder at the end of
the body.  `if.end198.i.i` forms the two numbers the fold starts from — the
mantissa head `%conv202.i.i` (the widen of `%top.0709.i.i`) and the residual
decimal exponent `%e10.0.i.i` — and the two loops that follow apply the ladder
one table row at a time: `while.body206.i.i` multiplies by `NUMF_EL1_POW10[%124]`
while the exponent is positive, `while.body232.i.i` divides by it while the
exponent is negative.  `while.end253.i.i` hands the doubled value's bits on.

**The emitted double.**  `t3Approx` is that fold at its own two operations: the
widen's rounding and one `fmul` or `fdiv` by the table's row.  The per-operation
bounds are `fmulBits_dist_le_step` and `fdivBits_dist_le_step` — one lattice step
each, at the tree's own `roundMag` — and `t3Approx_step` reads those at
`t3Approx`.

**The two-step error.**  A rounding at the widen and a rounding at the scaling
put the exact value within a step of the approximation and every boundary the
walk compares within a step of it; `proximity_scale` charges two steps each, and
`t3Fold_two_step` is the composition at the one approximation.  That is the
bracket `t3_scale_of_ulp` consumes, so the scale hypothesis of the sticky branch
is the fold's arithmetic rather than a property of a platform conversion.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.StrtodTier3

namespace NumFastTier3Fold

/-! ### The blocks that produce the fold's two inputs -/

/-- The block that forms the approximation's inputs: the residual exponent
`%sub200.i.i` and the widened mantissa head `%conv202.i.i`. -/
def t3TopBlock : String := "if.end198.i.i"

/-- The loop that multiplies by the table's rows while the exponent is
positive. -/
def t3MulBlock : String := "while.body206.i.i"

/-- The loop that divides by the table's rows while the exponent is
negative. -/
def t3DivBlock : String := "while.body232.i.i"

theorem t3TopBlock_eq : t3TopBlock = "if.end198.i.i" := rfl

theorem t3MulBlock_eq : t3MulBlock = "while.body206.i.i" := rfl

theorem t3DivBlock_eq : t3DivBlock = "while.body232.i.i" := rfl

/-! ### `if.end198.i.i` at its pin -/

/-- The block's instructions. -/
def t3FoldInstrs : List Instr :=
  [Instr.binop "%reass.sub" (BinOp.sub) 64 (Operand.reg "%add110.i.i")
     (Operand.reg "%topn.0711.i.i"),
   Instr.binop "%sub200.i.i" (BinOp.add) 64 (Operand.reg "%reass.sub")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.uitofp "%conv202.i.i" 64 (Operand.reg "%top.0709.i.i")]

theorem t3_fold_find :
    numFastBody.findBlock "if.end198.i.i" =
      some ⟨"if.end198.i.i", t3FoldInstrs, Term.br "while.cond203.i.i"⟩ := by
  simpa only [t3FoldInstrs] using numFast_findBlock_if_end198_i_i

/-- The environment the fold's first block leaves: the residual exponent and the
widened mantissa head. -/
def t3FoldEnv (env : Env) (u re : BitVec 64) (top : Nat) : Env :=
  ("%conv202.i.i", .float (uitofpBits top)) ::
  ("%sub200.i.i", .int 64 ((u - re) + 0x1#64)) ::
  ("%reass.sub", .int 64 (u - re)) :: env

/-- The block's chain: `%e10.0` is `%add110 - %topn + 1`, and `%conv202` is
`%top`'s widen — the two numbers the ladder starts from. -/
theorem t3_fold_denote {calls : Calls} {env : Env} {s : State}
    {u re top : BitVec 64}
    (hu : lookupName env "%add110.i.i" = some (.int 64 u))
    (hr : lookupName env "%topn.0711.i.i" = some (.int 64 re))
    (ht : lookupName env "%top.0709.i.i" = some (.int 64 top)) :
    denoteCode calls t3FoldInstrs (stateAt env s) =
      some (stateAt (t3FoldEnv env u re top.toNat) s) := by
  unfold t3FoldInstrs
  rw [denoteCode_sub_reg calls env s "%reass.sub" "%add110.i.i" "%topn.0711.i.i" hu hr]
  rw [denoteCode_add_imm calls (("%reass.sub", .int 64 (u - re)) :: env) s
    "%sub200.i.i" "%reass.sub" (lookupName_cons_self ..)]
  rw [denoteCode_uitofp calls
    (("%sub200.i.i", .int 64 (u - re + 0x1#64)) :: ("%reass.sub", .int 64 (u - re)) :: env)
    s "%conv202.i.i" "%top.0709.i.i" 64
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)];
        exact ht)]
  simp only [denoteCode_nil, t3FoldEnv, stateAt]

/-- The block's step: it writes no memory and jumps to the ladder's test. -/
theorem t3_fold_step {calls : Calls} {env : Env} {s : State}
    {u re top : BitVec 64}
    (hpc : s.pc = "if.end198.i.i")
    (hu : lookupName env "%add110.i.i" = some (.int 64 u))
    (hr : lookupName env "%topn.0711.i.i" = some (.int 64 re))
    (ht : lookupName env "%top.0709.i.i" = some (.int 64 top)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3FoldEnv env u re top.toNat)
        { s with pc := "while.cond203.i.i", pre := some "if.end198.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3FoldEnv env u re top.toNat) s)
    (b := ⟨"if.end198.i.i", t3FoldInstrs, Term.br "while.cond203.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_fold_find
  · simpa only [stateAt] using t3_fold_denote (calls := calls) hu hr ht
  · simp only [execTerm, stateAt, hpc]

/-! ### The ladder's two operations at their blocks

`while.body206.i.i` and `while.body232.i.i` each apply one table row to the
carried double; the cells below are those applications at the blocks' own pins,
so the fold's second operation is the emitted instruction and not a model of it. -/

theorem t3_mul_find :
    numFastBody.findBlock "while.body206.i.i" =
      some ⟨"while.body206.i.i",
        [Instr.icmp "%124.min" (IPred.ult) 64 (Operand.reg "%e10.0.i.i")
          (Operand.imm (Const.int 64 0x0000000000000016#64)),
         Instr.select "%124" (Ty.int 64) (Operand.reg "%124.min")
          (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
         Instr.gep "%arrayidx216.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10")
          (Operand.reg "%124"),
         Instr.load "%125" Ty.double (Operand.reg "%arrayidx216.i.i"),
         Instr.fmul "%mul217.i.i" (Operand.reg "%d201.0.i.i") (Operand.reg "%125"),
         Instr.binop "%sub219.i.i" (BinOp.sub) 64 (Operand.reg "%e10.0.i.i")
          (Operand.reg "%124"),
         Instr.bitcastToInt "%.cast.i.i.i" (Operand.reg "%mul217.i.i"),
         Instr.icmp "%cmp221.i.i" (IPred.ugt) 64 (Operand.reg "%.cast.i.i.i")
          (Operand.imm (Const.int 64 0x7fefffffffffffff#64))],
        Term.condbr (Operand.reg "%cmp221.i.i") "while.cond229.i.i.preheader"
          "while.cond203.i.i"⟩ := by
  simpa only using numFast_findBlock_while_body206_i_i

theorem t3_div_find :
    numFastBody.findBlock "while.body232.i.i" =
      some ⟨"while.body232.i.i",
        [Instr.icmp "%cmp234.i.i" (IPred.ult) 64 (Operand.reg "%e10.2.i.i")
          (Operand.imm (Const.int 64 0xffffffffffffffea#64)),
         Instr.binop "%.neg.i.i" (BinOp.mul) 64 (Operand.reg "%e10.2.i.i")
          (Operand.imm (Const.int 64 0xffffffff00000000#64)),
         Instr.binop "%126" (BinOp.ashr) 64 (Operand.reg "%.neg.i.i")
          (Operand.imm (Const.int 64 0x0000000000000020#64)),
         Instr.select "%idxprom242.i.i" (Ty.int 64) (Operand.reg "%cmp234.i.i")
          (Operand.imm (Const.int 64 0x0000000000000016#64)) (Operand.reg "%126"),
         Instr.gep "%arrayidx243.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10")
          (Operand.reg "%idxprom242.i.i"),
         Instr.load "%127" Ty.double (Operand.reg "%arrayidx243.i.i"),
         Instr.fdiv "%div.i.i" (Operand.reg "%d201.2.i.i") (Operand.reg "%127"),
         Instr.binop "%add245.i.i" (BinOp.add) 64 (Operand.reg "%idxprom242.i.i")
          (Operand.reg "%e10.2.i.i"),
         Instr.fcmp "%cmp246.i.i" (FPred.oeq) (Operand.reg "%div.i.i")
          (Operand.imm (Const.float 0x0000000000000000#64))],
        Term.condbr (Operand.reg "%cmp246.i.i") "while.end253.i.i" "while.cond229.i.i"⟩ := by
  simpa only using numFast_findBlock_while_body232_i_i

/-- The multiply's cell: the carried double times the table's row. -/
theorem t3_fmul217 (calls : Calls) (env : Env) (s : State) {x y : BitVec 64}
    (hd : lookupName env "%d201.0.i.i" = some (.float x))
    (hp : lookupName env "%125" = some (.float y)) :
    evalInstr calls (stateAt env s)
        (Instr.fmul "%mul217.i.i" (Operand.reg "%d201.0.i.i") (Operand.reg "%125")) =
      some (stateAt (("%mul217.i.i", .float (fmulBits x y)) :: env) s) :=
  step_fmul calls env s "%mul217.i.i" "%d201.0.i.i" "%125" hd hp

/-- The division's cell: the carried double over the table's row. -/
theorem t3_fdiv (calls : Calls) (env : Env) (s : State) {x y : BitVec 64}
    (hd : lookupName env "%d201.2.i.i" = some (.float x))
    (hp : lookupName env "%127" = some (.float y)) :
    evalInstr calls (stateAt env s)
        (Instr.fdiv "%div.i.i" (Operand.reg "%d201.2.i.i") (Operand.reg "%127")) =
      some (stateAt (("%div.i.i", .float (fdivBits x y)) :: env) s) :=
  step_fdiv calls env s "%div.i.i" "%d201.2.i.i" "%127" hd hp

/-! ### The emitted double and its per-operation bounds -/

/-- The fold at its two operations: the widened head (`t3FoldEnv`'s
`%conv202.i.i`) scaled by one table row, multiplying on the positive side and
dividing on the negative one. -/
def t3Approx (top p : BitVec 64) (div : Bool) : BitVec 64 :=
  if div then fdivBits top p else fmulBits top p

theorem t3Approx_mul (top p : BitVec 64) : t3Approx top p false = fmulBits top p := rfl

theorem t3Approx_div (top p : BitVec 64) : t3Approx top p true = fdivBits top p := rfl

/-- **One operation's error.**  The emitted double's ticks are the rounded
product's code, and the product is within one lattice step of the exact one — the
`while.body206.i.i` half of the fold. -/
theorem t3Approx_mul_step {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag)
    (hno : ¬ overflowTicks * 2 ^ 1074 ≤ c₁.ticks * c₂.ticks)
    {c : Code} (hc : roundMag (c₁.ticks * c₂.ticks) (2 ^ 1074) = .fin c) :
    F64.magTicks (F64.ofBits
        (t3Approx (packMag (.fin c₁) false) (packMag (.fin c₂) false) false)) = c.ticks ∧
      distNum (c₁.ticks * c₂.ticks) (2 ^ 1074) c.ticks
        ≤ 2 ^ 1074 * t3RoundStep (c₁.ticks * c₂.ticks) (2 ^ 1074) := by
  rw [t3Approx_mul]
  exact fmulBits_dist_le_step h₁ h₂ hno hc

/-- **One operation's error, the quotient's half.** -/
theorem t3Approx_div_step {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag)
    (hpos : 0 < c₂.ticks)
    (hno : ¬ overflowTicks * c₂.ticks ≤ c₁.ticks * 2 ^ 1074)
    {c : Code} (hc : roundMag (c₁.ticks * 2 ^ 1074) c₂.ticks = .fin c) :
    F64.magTicks (F64.ofBits
        (t3Approx (packMag (.fin c₁) false) (packMag (.fin c₂) false) true)) = c.ticks ∧
      distNum (c₁.ticks * 2 ^ 1074) c₂.ticks c.ticks
        ≤ c₂.ticks * t3RoundStep (c₁.ticks * 2 ^ 1074) c₂.ticks := by
  rw [t3Approx_div]
  exact fdivBits_dist_le_step h₁ h₂ hpos hno hc

/-! ### The two-step error

The widen rounds once and the scaling rounds once, so the exact value is within
one step of the approximation and every boundary the walk compares is within one
step of it; `proximity_scale` charges two steps each and `t3_scale_of_ulp`
consumes the result. -/

/-- **The fold's two-step error.**  Write `w` for the approximation's ticks, `u`
for the larger of the two operations' steps, `V` for the exact value and `B` for a
boundary the walk compares.  One step each side is inside the two steps
`proximity_scale` charges, so the boundary is at least half the value —
`t3_scale_of_ulp`'s premise at `2 * u`. -/
theorem t3Fold_two_step {V w B sV sB u : Nat}
    (hV : V ≤ w + sV) (hB : w ≤ B + sB) (hsV : sV ≤ u) (hsB : sB ≤ u)
    (hw : 6 * u ≤ w) : V ≤ 2 * B :=
  proximity_scale (by omega) (by omega) hw

/-- **The fold from the approximation to the shift.**  At the tree's own
rounding the scale hypothesis `t3_scale_of_ulp` takes is the fold's two-step
bracket, so the sticky branch's shift is a right shift because of the emitted
arithmetic. -/
theorem t3Fold_scale {m : Nat} {E : Int} {J : Nat} {eB : Int} {w u : Nat}
    (hm : 0 < m) (hJ : J < 2 ^ 54) (heB : -1075 ≤ eB) (hlead : leadM m E ≤ 308)
    (hV : valNum m E * twoDen eB
      ≤ w * (tenDen E * twoDen eB) + 2 * (u * (tenDen E * twoDen eB)))
    (hB : w * (tenDen E * twoDen eB)
      ≤ boundNum J eB * tenDen E + 2 * (u * (tenDen E * twoDen eB)))
    (hw : 6 * (u * (tenDen E * twoDen eB)) ≤ w * (tenDen E * twoDen eB)) :
    leadM m E - 767 ≤ eB :=
  t3_scale_of_ulp hm hJ heB hlead hV hB hw

/-! ### Axiom footprints -/

#print axioms t3_fold_denote
#print axioms t3_fold_step
#print axioms t3_fmul217
#print axioms t3_fdiv
#print axioms t3Approx_mul_step
#print axioms t3Approx_div_step
#print axioms t3Fold_two_step
#print axioms t3Fold_scale

end NumFastTier3Fold

end LeanLLVM.Refinement
