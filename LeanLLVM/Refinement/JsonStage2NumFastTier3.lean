/-
Tier 3 at the body: what the poison edges are, and where the traversal stops.

`JsonStage2NumFastArm` names the fallback's region — the inlined `num_scan`
second reader and the inlined `to_double` — and three links between the model
(`StrtodTier3.tier3Mag`) and the body's blocks: a `runFuel` simulation of the
region, the tie of the window's retained digits `M`, its scale `S` and the
sticky bit to `Decimal.mantissa`/`exponent`/`stkDrop`, and the proximity
estimate the tier-3 module still records.  This module states the first
obstruction of the first link and records the boundary of the other two.

**The poison edges are locally `ub`.**  `to_double`'s peeled loop nests carry
leading `phi`s whose entry-edge operands are `poison` immediates — e.g.
`while.cond.preheader.i.i577.i.i.unr-lcssa`'s `%add4.i.i572.i.i.lcssa.ph` and
`%shr.i.i574.i.i.lcssa.ph.off0` from `for.body.lr.ph.i.i564.i.i`.  The model has
no poison: `Const.toValue` answers a `poison` literal with `none`, so
`evalOperand` refuses it, `phiSelect` is `none`, the block's `denoteCode` is
`none`, and `step` is `.ub`.  The lemmas below are that chain at the block's own
pin: `phiSelect_poison`, `denoteCode_poison_head`, and the block-level
`t3_poison_edge_ub`.

**What that is not.**  A locally `ub` edge is not an unreachable one.  The
`runFuel` simulation must show the edge is never taken on a lexeme the fallback
reaches, which is a trip-count fact about the peeled nests
(`for.body.lr.ph.i.i564.i.i` is the zero-trip entry of the `1088`-iteration
loop nest, and the region's own guard decides whether it is entered).  The tree
has no step lemma for any block of the region, so the simulation that would
carry that argument does not exist; this module records the local obstruction
and names the entry trip count as the first thing the simulation must decide.

**The window tie.**  `StrtodTier3.windowOf`'s `M`, `S` and `sticky` are the
model; the body's `for.body87.i.i` window copy enforces `STK_DIGITS` and the
`for.body.i.i` parse accumulates the digits.  No theorem in the tree relates the
copy loop's retained window to `stkDrop`, so the tie is the second open link.

**The proximity estimate.**  Its two operations are `fmulBits` and `fdivBits`,
which `JsonStage2NumFastTier1` defines and proves at the tree's own bit model
(`fmulBits_pack`, `fdivBits_pack`, `fdivBits_uitofp_pow`), so the estimate does
not rest on a hardware model.  What it still needs is the ulp inequality on the
approximation `dbits (d) * 10 ^ e10` — an arithmetic fact about the model, not a
bit-level step — and that inequality is not stated in the tree.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier1
import LeanLLVM.StrtodTier3

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

namespace NumFastTier3

/-! ### A poison `phi` edge reads nothing

`Const.toValue` refuses `poison` and `undef`, so an edge whose incoming operand
is a poison immediate makes the `phi` selection `none`.  The two lemmas are the
model's own vocabulary, not a statement about a particular block. -/

theorem evalOperand_poison (s : State) :
    evalOperand s (.imm Const.poison) = none := rfl

theorem phiSelect_poison {s : State} {p : String} {inc : List (String × Operand)}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison)) :
    phiSelect s inc = none := by
  simp [phiSelect, hpre, hinc, evalOperand_poison]

/-- A block whose leading `phi` run selects a poison immediate on the edge the
state names has no `denoteCode`: the run stops before its first member lands. -/
theorem denoteCode_poison_head {calls : Calls} {s : State} {p : String}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {rest : List Instr}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison)) :
    denoteCode calls (.phi d ty inc :: rest) s = none := by
  unfold denoteCode denoteRun
  rw [phiSelect_poison hpre hinc]

/-! ### The peeled nest's entry edge

`while.cond.preheader.i.i577.i.i.unr-lcssa` is the first `to_double` block with a
poison-carrying `phi` run.  Its pin is the literal; the step from the
zero-trip entry is `ub` at every `Calls` and staging, because the first `phi`'s
incoming from that predecessor is `Const.poison`. -/

/-- The block's step from `for.body.lr.ph.i.i564.i.i` is `ub`: the first `phi`
selects a poison immediate. -/
theorem t3_poison_edge_ub (calls : Calls) (env : Env) (s : State) :
    step calls numFastBody
      (stateAt env ({ s with pc := "while.cond.preheader.i.i577.i.i.unr-lcssa", pre := some "for.body.lr.ph.i.i564.i.i" })) = .ub := by
  have hfind := numFast_findBlock_while_cond_preheader_i_i577_i_i_unr_lcssa
  simp [step, stateAt, hfind, denoteCode, denoteRun, phiSelect, phiIncoming,
    evalOperand, Const.toValue, State.bindAll]

/-- The same edge one `runFuel` step in: the run stops at `ub`. -/
theorem t3_poison_edge_runFuel_ub (calls : Calls) (env : Env) (s : State) (k : Nat) :
    runFuel calls (k + 1) numFastBody
      (stateAt env ({ s with pc := "while.cond.preheader.i.i577.i.i.unr-lcssa", pre := some "for.body.lr.ph.i.i564.i.i" })) = some .ub := by
  simp only [runFuel, t3_poison_edge_ub]

/-! ### The boundary, recorded

The three links `JsonStage2NumFastArm` lists for this region, and what the tree
supplies for each:

* **The run.**  The region runs from `if.end285` (`num_scan`'s inline second
  reader) through `to_double` to `if.end291`'s store.  No block of it has a step
  lemma, and its entry edges from the peeled nests carry poison immediates; the
  `ub` above is the local obstruction.  The trip count that would prove the
  edge unreachable — `for.body.lr.ph.i.i564.i.i` is the zero-trip entry of the
  peeled nest — is not in the tree, so the simulation is not built.
* **The window tie.**  `StrtodTier3.windowOf` defines `M`, `S` and `sticky`
  (`windowOf_sticky_iff` is the model's own reading), while the body's
  `for.body87.i.i` copy enforces `STK_DIGITS` and `for.body.i.i` accumulates
  the digits.  No theorem relates the copy loop's window to `stkDrop`, so the
  tie between them is open.
* **The proximity estimate.**  Its operations are `fmulBits` and `fdivBits`,
  which `JsonStage2NumFastTier1` defines and proves at the tree's bit model
  (`fmulBits_pack`, `fdivBits_pack`, `fdivBits_uitofp_pow`), so the estimate
  does not rest on hardware.  What remains is the ulp inequality on the
  approximation `dbits (d) * 10 ^ e10`, an arithmetic fact about the model that
  the tree does not state.

None of the three is a `sorry`; they are open statements, and the module above
proves the first block-level fact the first one needs. -/

end NumFastTier3

/-! ### Axiom footprints -/

#print axioms NumFastTier3.phiSelect_poison
#print axioms NumFastTier3.denoteCode_poison_head
#print axioms NumFastTier3.t3_poison_edge_ub
#print axioms NumFastTier3.t3_poison_edge_runFuel_ub

end LeanLLVM.Refinement
