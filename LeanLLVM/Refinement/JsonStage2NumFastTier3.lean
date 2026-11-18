/-
Tier 3 at the body: the poison edges, the traversal with the trip count, the
window's copy, and the proximity estimate.

`JsonStage2NumFastArm` names the fallback's region — the inlined `num_scan`
second reader and the inlined `to_double` — and three links between the model
(`StrtodTier3.tier3Mag`) and the body's blocks: a `runFuel` simulation of the
region, the tie of the window's retained digits `M`, its scale `S` and the
sticky bit to `Decimal.mantissa`/`exponent`/`stkDrop`, and the proximity
estimate.  This module states the first link's poison edge and composes it with
the trip count, states the second link's three pieces and the copy's own store,
and proves the third link's inequality at the tree's rounding.  What remains of
the region is its other blocks, named at the end.

**The poison edges bind the marker; the block reads neither cell.**  `to_double`'s
peeled loop nests carry leading `phi`s whose entry-edge operands are `poison`
immediates — e.g. `while.cond.preheader.i.i577.i.i.unr-lcssa`'s
`%add4.i.i572.i.i.lcssa.ph` and `%shr.i.i574.i.i.lcssa.ph.off0` from
`for.body.lr.ph.i.i564.i.i`.  A `poison` literal read as an instruction's own
operand is `ub` (`Const.toValue` answers it `none`), but a `phi`'s taken incoming
is not that read: LLVM's `phi` over a poison incoming yields poison, and the use
that reads the destination is where the poison becomes `ub`.  `phiSelect`
therefore binds `Value.poison` into the destination, `evalOperand` refuses the
marker at the read, and a block that does not read the cell is unaffected.  The
residual block is exactly that block: its only remaining instruction is the
`%lcmp.mod1085.not` test, which reads `%xtraiter1083` and neither poison cell, so
its own step is the terminator's jump.  The lemmas below are that pair at the
block's own pin: `phiSelect_poison`, the pending-binding `denoteRun_poison_head`,
`denoteCode_poison_head` for a rest that is not a `phi` run, the read-conditional
`denoteCode_poison_head_ub`, and the block-level
`t3_poison_edge_step_one`/`t3_poison_edge_step_zero` with
`t3_poison_edge_runFuel`.

**The traversal with the trip count.**  A defined edge is not yet a traversal, so
the entry's choice is composed with it.  `for.body.lr.ph.i.i564.i.i` tests
`%inc12.us.i.i581759761.i.i <u 4`, and the caller excludes only zero, so a
peeled count in `0 < k < 4` takes the residual edge exactly
(`t3_entry_step_residual`); on that edge the residual block's `%xtraiter1083` is
the count itself (`t3_xtraiter_ofNat`, `t3_entry_residual_bit`), so its residue
test is refused and it jumps to the epilogue.  `t3_traversal_counts_1_3` is that
pair as two `runFuel` steps, the state it reaches is named, and
`t3_traversal_markers` reads the reached state's two `poison` cells as markers
that no read can observe.  The region's simulation therefore continues at
`for.body.i.i566.i.i.epil` rather than at `.ub`.

**The epilogue chain.**  The block the traversal hands to is the copy's last
group: three carried `phi`s, the table row read at `%pow.i.i + 8 * %indvars`, the
widen to `i128`, the `10 ^ 19` multiply and the carry's addition, the low word's
store, the high word's `lshr` by sixty-four, the two increments, and the residue
test.  `t3_epil_denote` is that block's chain at its pin, `t3_epil_step_lcssa`
and `t3_epil_step_self` are its two successors, and the three `i128` operations
the chain needs beyond the existing steps (`mul` with an immediate, `add` of two
registers, `lshr` with an immediate) are stated width-generically
(`step_mul_imm_w`/`denoteCode_mul_imm_w`, `step_add_reg_w`/`denoteCode_add_reg_w`,
`step_lshr_imm_w`/`denoteCode_lshr_imm_w`).  `t3PowConst` is `10 ^ 19`, the table
row the copy reads past the nineteen it retains, and the shift's amount is the
word's high half.

**The window tie.**  `StrtodTier3.windowOf`'s `M`, `S` and `sticky` are the
model; the body's copy writes the significant digits into its 768-byte array,
sets one sticky bit for the digits past it, and counts `T`, `lead`, `F` and `R`.
`copy_retained` is the retained array read as an integer equal to `m / 10 ^
stkDrop m`, `copy_sticky` is the copy's sticky bit equal to the model's
remainder test, and `copy_counters` reads the emitted scale
`S = exp10 - F + (nsig - R)` as `E + stkDrop m` and its leading exponent
`f = (R - 1) + S` as `leadM`.  The three `_window` forms state the same at the
model's own fields: `copy_retained_window` is `.M`, `copy_sticky_window` is
`.sticky`, `copy_S_window` is `.S`, and `copy_lead_window` is `.lead` — so the
body's two clamps at `f` are `roundMag`'s.  `t3_copy_denote` steps the block that
performs the store, `if.then31.i.i`, so the digit the loop's register carries is
the byte the array holds.

**The proximity estimate.**  Its operations are `fmulBits` and `fdivBits`, which
`JsonStage2NumFastTier1` defines and proves at the tree's own bit model
(`fmulBits_pack`, `fdivBits_pack`, `fdivBits_uitofp_pow`): each is `packMag` of
one `roundMag`, so the estimate is a statement about the tree's rounding and not
about hardware.  `roundMag_dist_le_step` bounds one rounding by one lattice step
in either branch, `fmulBits_dist_le_step`/`fdivBits_dist_le_step` are that bound
at the two operations, `proximity_scale` composes the two-step bracket into
`V ≤ 2 * B`, and `t3_scale_of_ulp` concludes `valLeqBoundary m E (2 * J) eB` —
exactly the premise `StrtodTier3.shift_of_near` consumes — so the shift the
sticky branch performs is a right shift because of the tree's own rounding.
-/

import LeanLLVM.Refinement.JsonStage2NumFastTier1
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.StrtodTier3

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1100

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

namespace NumFastTier3

/-! ### A poison `phi` edge binds the marker

`Const.toValue` refuses `poison` and `undef`, so a poison immediate read as an
instruction's own operand is `ub`.  A `phi`'s taken incoming is a different
thing: LLVM's `phi` over a poison incoming yields poison, not undefined
behaviour, and the use that reads the destination is where it becomes `ub`.
`phiSelect` binds `Value.poison` into the destination for exactly that case,
`evalOperand` refuses the marker at the read, and the lemmas below are that
pair.  Neither is a statement about a particular block. -/

theorem evalOperand_poison (s : State) :
    evalOperand s (.imm Const.poison) = none := rfl

/-- The selection of a poison incoming is the marker, not a failure: the edge is
defined, and the block's run continues from the cell it binds. -/
theorem phiSelect_poison {s : State} {p : String} {inc : List (String × Operand)}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison)) :
    phiSelect s inc = some .poison := by
  simp [phiSelect, hpre, hinc]

/-- The cell a poisoned `phi` binds has no value: a read of it is a use. -/
theorem evalOperand_poison_cell (s : State) (d : String) :
    evalOperand (s.bind d .poison) (.reg d) = none := by
  simp [evalOperand, State.bind]

/-- A leading `phi` that takes the poison literal on the state's edge adds the
marker to the run's pending bindings.  Nothing is installed by the `phi` itself:
a `phi`'s incoming read observes the environment, not the run's pending cells, so
the pending form is what the definition yields. -/
theorem denoteRun_poison_head {calls : Calls} {pend : List (String × Value)}
    {s : State} {p : String} {d : String} {ty : Ty} {inc : List (String × Operand)}
    {rest : List Instr}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison)) :
    denoteRun calls pend (.phi d ty inc :: rest) s =
      denoteRun calls (pend ++ [(d, .poison)]) rest s := by
  simp only [denoteRun, phiSelect_poison hpre hinc]

/-- A block whose leading `phi` takes the poison literal on the edge the state
names binds the marker; when the rest of the block is not itself a `phi` run the
pending binding installs at once, so the run continues from the state with the
cell set.  A rest that *is* a `phi` run cannot be collapsed this way: its own
incoming reads observe the pre-block environment, so the marker stays pending
until the first non-`phi` instruction. -/
theorem denoteCode_poison_head {calls : Calls} {s : State} {p : String}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {rest : List Instr}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison))
    (hrest : startsWithPhi rest = false) :
    denoteCode calls (.phi d ty inc :: rest) s =
      denoteCode calls rest (s.bind d .poison) := by
  rw [denoteCode, denoteRun_poison_head hpre hinc, denoteRun_nil_pend hrest]
  rfl

/-- **The read-conditional form.**  The block is `ub` at a remaining run that
reads the destination: the marker is in the cell and `evalOperand` refuses it.
This is what makes the marker observable only through a use. -/
theorem denoteCode_poison_head_ub {calls : Calls} {s : State} {p : String}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {i : Instr}
    {rest : List Instr}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison))
    (hi : i.isPhi = false) (hread : evalInstr calls (s.bind d .poison) i = none) :
    denoteCode calls (.phi d ty inc :: i :: rest) s = none := by
  have hrest : startsWithPhi (i :: rest) = false := by
    cases i <;> simp_all [startsWithPhi, Instr.isPhi]
  rw [denoteCode_poison_head hpre hinc hrest]
  exact denoteCode_cons_none calls i rest (s.bind d .poison) hread hi

/-! ### The peeled nest's entry edge

`while.cond.preheader.i.i577.i.i.unr-lcssa` is the first `to_double` block with a
poison-carrying `phi` run.  Its pin is the literal.  From the zero-trip entry the
two poisoned `phi`s bind the marker, the two well-defined ones bind their
immediates, and the block's remaining instruction — the `%lcmp.mod1085.not` test
— reads `%xtraiter1083`, which the entry block computed.  Neither poison cell is
read, so the block's own step is the terminator's jump at every `Calls` and
staging. -/

/-- The block's leading `phi` run, from its pin. -/
def t3ResidualPhis : List Instr :=
  [Instr.phi "%add4.i.i572.i.i.lcssa.ph" (Ty.int 128)
     [("for.body.lr.ph.i.i564.i.i", Operand.imm Const.poison),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit",
        Operand.reg "%add4.i.i572.i.i.3")],
   Instr.phi "%shr.i.i574.i.i.lcssa.ph.off0" (Ty.int 64)
     [("for.body.lr.ph.i.i564.i.i", Operand.imm Const.poison),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit",
        Operand.reg "%extract.t1099")],
   Instr.phi "%indvars.iv.i.i567.i.i.unr" (Ty.int 64)
     [("for.body.lr.ph.i.i564.i.i", Operand.imm (Const.int 64 0x0000000000000000#64)),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit",
        Operand.reg "%indvars.iv.next.i.i575.i.i.3")],
   Instr.phi "%carry.029.i.i568.i.i.unr" (Ty.int 128)
     [("for.body.lr.ph.i.i564.i.i",
        Operand.imm (Const.int 128 0x00000000000000000000000000000000#128)),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit",
        Operand.reg "%shr.i.i574.i.i.3")]]

/-- The block's instructions: its `phi` run, then the residue test. -/
def t3ResidualInstrs : List Instr :=
  t3ResidualPhis ++
    [Instr.icmp "%lcmp.mod1085.not" (IPred.eq) 64 (Operand.reg "%xtraiter1083")
      (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem t3_findBlock_residual :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i.unr-lcssa" =
      some ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", t3ResidualInstrs,
        Term.condbr (Operand.reg "%lcmp.mod1085.not")
          "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩ := by
  simpa only [t3ResidualInstrs, t3ResidualPhis, List.cons_append, List.nil_append,
    List.singleton_append] using
    numFast_findBlock_while_cond_preheader_i_i577_i_i_unr_lcssa

/-- The environment the run leaves: the four `phi` cells, the test, and the
incoming environment.  Both poisoned destinations hold the marker. -/
def t3ResidualEnv (env : Env) (x : BitVec 64) : Env :=
  ("%lcmp.mod1085.not", .int 1 (evalICmp .eq x 0)) ::
  ("%carry.029.i.i568.i.i.unr", .int 128 0) ::
  ("%indvars.iv.i.i567.i.i.unr", .int 64 0) ::
  ("%shr.i.i574.i.i.lcssa.ph.off0", .poison) ::
  ("%add4.i.i572.i.i.lcssa.ph", .poison) :: env

/-- The residual block's run at the peeled count's residue: the marker, the two
immediates, the test, and the incoming environment. -/
theorem t3_residual_denote {calls : Calls} {env : Env} {s : State} {x : BitVec 64}
    (hpc : s.pre = some "for.body.lr.ph.i.i564.i.i")
    (hx : lookupName env "%xtraiter1083" = some (.int 64 x)) :
    denoteCode calls t3ResidualInstrs (stateAt env s) =
      some (stateAt (t3ResidualEnv env x) s) := by
  simp [t3ResidualInstrs, t3ResidualPhis, denoteCode, denoteRun, phiSelect,
    phiIncoming, evalOperand, lookupName, evalInstr, Const.toValue, hpc, hx,
    Value.intToNat, evalICmpNat, evalICmp, State.bindAll, State.bind, t3ResidualEnv, stateAt]

/-- The two poison cells hold the marker, so each has no value at the read. -/
theorem t3_poison_cells_unread (env : Env) (s : State) (x : BitVec 64) :
    evalOperand (stateAt (t3ResidualEnv env x) s) (.reg "%add4.i.i572.i.i.lcssa.ph") = none ∧
    evalOperand (stateAt (t3ResidualEnv env x) s)
      (.reg "%shr.i.i574.i.i.lcssa.ph.off0") = none := by
  refine ⟨?_, ?_⟩ <;> simp [t3ResidualEnv, stateAt, evalOperand, lookupName]

/-- **The read-conditional form at the block.**  The same `phi` run with its test
reading a poison cell instead of `%xtraiter1083` has no `denoteCode`: the cell
holds the marker and the read is the use.  The block does not do this, which is
why its own step is the jump below. -/
theorem t3_poison_edge_ub {calls : Calls} {env : Env} {s : State} :
    denoteCode calls
      (t3ResidualPhis ++
        [Instr.icmp "%lcmp.mod1085.not" (IPred.eq) 64
          (Operand.reg "%add4.i.i572.i.i.lcssa.ph")
          (Operand.imm (Const.int 64 0x0000000000000000#64))])
      (stateAt env { s with pre := some "for.body.lr.ph.i.i564.i.i" }) = none := by
  simp [t3ResidualPhis, denoteCode, denoteRun, phiSelect, phiIncoming,
    evalOperand, lookupName, evalInstr, Const.toValue, State.bindAll,
    State.bind, stateAt]

/-- The block's step from the zero-trip entry at residue one: the run lands the
five cells and the terminator jumps to the loop header. -/
theorem t3_poison_edge_step_one {calls : Calls} {env : Env} {s : State} {x : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.unr-lcssa")
    (hpre : s.pre = some "for.body.lr.ph.i.i564.i.i")
    (hx : lookupName env "%xtraiter1083" = some (.int 64 x))
    (hbit : evalICmp .eq x 0 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3ResidualEnv env x)
        { s with pc := "while.cond.preheader.i.i577.i.i",
                 pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (t3ResidualEnv env x) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", t3ResidualInstrs,
      Term.condbr (Operand.reg "%lcmp.mod1085.not")
        "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3ResidualInstrs] using t3_findBlock_residual
  · simpa only [stateAt] using t3_residual_denote (calls := calls) hpre hx
  · have hlk : lookupName (t3ResidualEnv env x) "%lcmp.mod1085.not"
        = some (.int 1 (evalICmp .eq x 0)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%lcmp.mod1085.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The block's step from the zero-trip entry at residue zero: the same run, and
the terminator jumps to the peeled nest. -/
theorem t3_poison_edge_step_zero {calls : Calls} {env : Env} {s : State} {x : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.unr-lcssa")
    (hpre : s.pre = some "for.body.lr.ph.i.i564.i.i")
    (hx : lookupName env "%xtraiter1083" = some (.int 64 x))
    (hbit : evalICmp .eq x 0 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3ResidualEnv env x)
        { s with pc := "for.body.i.i566.i.i.epil",
                 pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (t3ResidualEnv env x) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", t3ResidualInstrs,
      Term.condbr (Operand.reg "%lcmp.mod1085.not")
        "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3ResidualInstrs] using t3_findBlock_residual
  · simpa only [stateAt] using t3_residual_denote (calls := calls) hpre hx
  · have hlk : lookupName (t3ResidualEnv env x) "%lcmp.mod1085.not"
        = some (.int 1 (evalICmp .eq x 0)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%lcmp.mod1085.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The same edge one `runFuel` step in: the run continues from the jump. -/
theorem t3_poison_edge_runFuel {calls : Calls} {env : Env} {s : State} {x : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.unr-lcssa")
    (hpre : s.pre = some "for.body.lr.ph.i.i564.i.i")
    (hx : lookupName env "%xtraiter1083" = some (.int 64 x))
    (hbit : evalICmp .eq x 0 = (1 : BitVec 1)) (k : Nat) :
    runFuel calls (k + 1) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (t3ResidualEnv env x)
          { s with pc := "while.cond.preheader.i.i577.i.i",
                   pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) := by
  simp only [runFuel, t3_poison_edge_step_one hpc hpre hx hbit]

/-! ### The boundary, recorded

The three links `JsonStage2NumFastArm` lists for this region, what the tree now
supplies for each, and what is left:

* **The run.**  The region runs from `if.end285` (`num_scan`'s inline second
  reader) through `to_double` to `if.end291`'s store.  The peeled nest's entry is
  stepped (`t3_entry_step_residual`/`t3_entry_step_unrolled`): its test is
  `%inc12 <u 4`, and the caller excludes only zero, so the residual edge is taken
  exactly at a peeled count below four.  The residual block's own step is
  supplied (`t3_poison_edge_step_one`/`t3_poison_edge_step_zero`), and the two
  are composed into the traversal at the count (`t3_traversal_counts_1_3`), with
  the reached state's markers unread (`t3_traversal_markers`).  The traversal's
  handoff is chained through the epilogue block itself (`t3_epil_denote` and its
  two successors `t3_epil_step_lcssa`/`t3_epil_step_self`).  The copy loop's
  blocks are then stepped per edge in `JsonStage2NumFastTier3CopySteps` — the
  head, the three unrolled tests, the store and both latches, each at its own
  predecessor — so what is still open is the loop's two `BoundLoop` instances,
  the unrolled nest's and the residual one's; the starting approximation's fold
  is `JsonStage2NumFastTier3Fold`'s.
* **The window tie.**  `StrtodTier3.windowOf` defines `M`, `S` and `sticky`
  (`windowOf_sticky_iff` is the model's own reading); the body's copy's retained
  array is that `M` (`copy_retained`), its stuck bit is that `sticky`
  (`copy_sticky`), and its counters `T`, `lead`, `F`, `R` give that `S` and that
  leading exponent (`copy_counters`).  The block that writes the array is stepped
  at its pin (`t3_copy_denote`), and the loop's own blocks are
  `JsonStage2NumFastTier3CopySteps`' per-edge steps.  What is not composed is
  the induction: the copy is unrolled four ways with an epilogue, so its
  `runFuel` simulation is two `BoundLoop` instances, one per loop.
* **The proximity estimate.**  Its operations are `fmulBits` and `fdivBits`,
  which `JsonStage2NumFastTier1` defines and proves at the tree's bit model
  (`fmulBits_pack`, `fdivBits_pack`, `fdivBits_uitofp_pow`), so the estimate does
  not rest on hardware.  `roundMag_dist_le_step` is the per-rounding bound and
  `proximity_scale` the two-step composition; `t3_scale_of_ulp` concludes
  `valLeqBoundary m E (2 * J) eB`, the premise `shift_of_near` takes.  What is
  not derived is the starting approximation's own fold: that the emitted
  `d` is exactly two `fmulBits`/`fdivBits` applications at the table's rows, and
  that its two-step error is the `2 * u` the hypothesis names, is the fold's
  arithmetic — one application of `fmulBits_dist_le_step` or
  `fdivBits_dist_le_step` per operation, at the scale `tenDen E * twoDen eB`.
  `JsonStage2NumFastTier3Fold` is that: which blocks form `top` and `e10`
  (`if.end198.i.i`), the two operations at their own pins (`while.body206.i.i`,
  `while.body232.i.i`), the emitted double `t3Approx`, its per-operation bound
  and the two-step composition `t3Fold_two_step`.

None of the three is a `sorry`; each is stated, and what remains is named above
rather than assumed. -/

/-! ### The peeled nest's entry: what decides the poison edge

`for.body.lr.ph.i.i564.i.i` is the block that chooses between the residual path
— `while.cond.preheader.i.i577.i.i.unr-lcssa`, whose two `phi`s carry `poison`
from this edge — and the four-way unrolled nest.  Its own test is
`%101 = (%inc12.us.i.i581759761.i.i <u 4)`, so the choice is the peeled count:
the residual path is taken **exactly** when the count is below four, and the
unrolled path when it is four or more.  The block's other two cells name the
count's width and its residue (`%wide.trip.count = zext %inc12`, `%xtraiter =
%wide.trip.count & 3`), which the residual path's own epilogue test reads.

What that fixes.  A trip-count argument that would make the residual edge
unreachable cannot be an argument about the peel itself: nothing at this block
excludes counts `1`, `2` or `3`, and the caller (`while.body173.i.i`) only
excludes zero.  On that path the two `poison` `phi`s bind the marker and the
block reads neither cell — its own instruction is the residue test, and the
emitted code reads only the two well-defined `phi`s (`%indvars…unr` and
`%carry…unr` are a `0` immediate each).  `t3_poison_edge_step_one`/
`t3_poison_edge_step_zero` are that step, and `t3_poison_edge_ub` is the
counterfactual: a run whose test read a poison cell would be `ub`.
`t3_residual_test_zero` reads the branch: for a count inside `0 < k < 4` the
residue is the count itself and the epilogue test is refused, so the residual
path is taken with the two markers bound and unread.  The residual obligation is
therefore not a trip-count bound the tree is missing and not a question about
the model's handling of an unread `poison` `phi`; it is the rest of the region's
`runFuel` simulation, block by block. -/

/-- The peeled nest's entry block, from its `findBlock` pin. -/
def t3EntryInstrs : List Instr :=
  [Instr.zext "%wide.trip.count.i.i565.i.i" 32 64
      (Operand.reg "%inc12.us.i.i581759761.i.i"),
   Instr.binop "%xtraiter1083" (BinOp.and) 64
      (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
   Instr.icmp "%101" (IPred.ult) 32 (Operand.reg "%inc12.us.i.i581759761.i.i")
      (Operand.imm (Const.int 32 0x0000000000000004#32))]

theorem t3_findBlock_entry :
    numFastBody.findBlock "for.body.lr.ph.i.i564.i.i" =
      some ⟨"for.body.lr.ph.i.i564.i.i", t3EntryInstrs,
        Term.condbr (Operand.reg "%101")
          "while.cond.preheader.i.i577.i.i.unr-lcssa" "for.body.lr.ph.i.i564.i.i.new"⟩ := by
  simpa only [t3EntryInstrs] using numFast_findBlock_for_body_lr_ph_i_i564_i_i

/-- The entry's environment: the width the count is widened to, its residue, and
the test's bit. -/
def t3EntryEnv (env : Env) (c : BitVec 32) : Env :=
  ("%101", .int 1 (evalICmp .ult c 0x00000004#32)) ::
  ("%xtraiter1083", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x3#64)) ::
  ("%wide.trip.count.i.i565.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env

/-- The entry block's chain at the peeled count. -/
theorem t3_entry_denote {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c)) :
    denoteCode calls t3EntryInstrs (stateAt env s) =
      some (stateAt (t3EntryEnv env c) s) := by
  unfold t3EntryInstrs
  rw [denoteCode_zext calls env s "%wide.trip.count.i.i565.i.i"
    "%inc12.us.i.i581759761.i.i" 32 64 hc _]
  rw [BlockEval.denoteCode_and_imm calls
    (("%wide.trip.count.i.i565.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env) _
    "%xtraiter1083" "%wide.trip.count.i.i565.i.i"
    (lookupName_cons_self ..) _]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%xtraiter1083", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x3#64)) ::
     ("%wide.trip.count.i.i565.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env) _
    "%101" "%inc12.us.i.i581759761.i.i" .ult (by
      rw [lookupName_cons_ne _ _ (by decide :
        ("%xtraiter1083" : String) ≠ "%inc12.us.i.i581759761.i.i")]
      rw [lookupName_cons_ne _ _ (by decide :
        ("%wide.trip.count.i.i565.i.i" : String) ≠ "%inc12.us.i.i581759761.i.i")]
      exact hc) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, t3EntryEnv]

/-- The entry's test at one: the peeled count is below four. -/
theorem t3_entry_101_iff {c : BitVec 32} :
    evalICmp .ult c 0x00000004#32 = (1 : BitVec 1) ↔ c.toNat < 4 := by
  rw [NumFastStarts.ult_iff_one,
    show (0x00000004#32).toNat = 4 from by decide]

/-- The residual edge: a count below four takes the block whose `phi`s carry the
edge's `poison`. -/
theorem t3_entry_step_residual {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i")
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c))
    (hlt : c.toNat < 4) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3EntryEnv env c)
        { s with pc := "while.cond.preheader.i.i577.i.i.unr-lcssa",
                 pre := some "for.body.lr.ph.i.i564.i.i" }) := by
  have hbit : evalICmp .ult c 0x00000004#32 = (1 : BitVec 1) :=
    t3_entry_101_iff.mpr hlt
  refine numFast_step_at (s' := stateAt (t3EntryEnv env c) s)
    (b := ⟨"for.body.lr.ph.i.i564.i.i", t3EntryInstrs,
      Term.condbr (Operand.reg "%101")
        "while.cond.preheader.i.i577.i.i.unr-lcssa" "for.body.lr.ph.i.i564.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3EntryInstrs] using t3_findBlock_entry
  · simpa only [denoteCode_nil] using t3_entry_denote (calls := calls) hc
  · have hlk : lookupName (t3EntryEnv env c) "%101"
        = some (.int 1 (evalICmp .ult c 0x00000004#32)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%101" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The unrolled edge: a count of four or more takes the four-way nest. -/
theorem t3_entry_step_unrolled {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i")
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c))
    (hge : 4 ≤ c.toNat) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3EntryEnv env c)
        { s with pc := "for.body.lr.ph.i.i564.i.i.new",
                 pre := some "for.body.lr.ph.i.i564.i.i" }) := by
  have hbit : evalICmp .ult c 0x00000004#32 = (0 : BitVec 1) := by
    rw [NumFastStarts.ult_zero_iff,
      show (0x00000004#32).toNat = 4 from by decide]
    omega
  refine numFast_step_at (s' := stateAt (t3EntryEnv env c) s)
    (b := ⟨"for.body.lr.ph.i.i564.i.i", t3EntryInstrs,
      Term.condbr (Operand.reg "%101")
        "while.cond.preheader.i.i577.i.i.unr-lcssa" "for.body.lr.ph.i.i564.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3EntryInstrs] using t3_findBlock_entry
  · simpa only [denoteCode_nil] using t3_entry_denote (calls := calls) hc
  · have hlk : lookupName (t3EntryEnv env c) "%101"
        = some (.int 1 (evalICmp .ult c 0x00000004#32)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%101" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- A count inside `0 < k < 4` has its own residue, so the residual path's
epilogue test is refused: the block reads only the two well-defined `phi`s. -/
theorem t3_residual_test_zero {k : Nat} (h0 : 0 < k) (h4 : k < 4) :
    evalICmp .eq (BitVec.ofNat 64 k &&& 0x3#64) (0 : BitVec 64) = 0 := by
  rw [NumFastStarts.eq_zero_iff]
  intro h
  have hk : BitVec.ofNat 64 k &&& 0x3#64 = BitVec.ofNat 64 k := by
    rw [← BitVec.ofNat_and]
    congr 1
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with h1 | h1 | h1 <;>
      rw [h1] <;> decide
  rw [hk] at h
  have hz := congrArg BitVec.toNat h
  have hzero : ((0 : BitVec 64)).toNat = 0 := rfl
  rw [hzero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)] at hz
  omega

/-! ### The traversal with the trip count

The entry's step and the residual block's step are complements at one count.
From the peeled entry a count below four takes the residual edge
(`t3_entry_step_residual`), and on that edge the residual block's `%xtraiter1083`
is the count itself, so its residue test is refused and the block jumps to the
epilogue (`t3_poison_edge_step_zero`).  The composition below is that pair as one
`runFuel` of two steps, with the state the run continues from named: the two
`poison` cells hold the marker, neither is read, and the continuation is the
epilogue block.  A simulation of the region no longer meets `.ub` at this edge;
it meets a state. -/

/-- Below four, the peeled count is its own remainder: the entry's `zext` to 64
then `& 3` leaves the count unchanged. -/
theorem t3_xtraiter_ofNat {c : BitVec 32} (h4 : c.toNat < 4) :
    BitVec.ofNat 64 c.toNat &&& 0x3#64 = BitVec.ofNat 64 c.toNat := by
  rcases (by omega : c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3) with h | h | h | h <;>
    rw [h] <;> decide

/-- At the entry's environment the residual block's `%xtraiter1083` is the
peeled count. -/
theorem t3_entryEnv_xtraiter {env : Env} {c : BitVec 32} (h4 : c.toNat < 4) :
    lookupName (t3EntryEnv env c) "%xtraiter1083"
      = some (.int 64 (BitVec.ofNat 64 c.toNat)) := by
  have hne : ("%101" : String) ≠ "%xtraiter1083" := by decide
  simp only [t3EntryEnv]
  rw [lookupName_cons_ne _ _ hne, lookupName_cons_self, t3_xtraiter_ofNat h4]

/-- At a count inside `0 < k < 4` the residual test is refused: the block reads
only the two well-defined `phi`s. -/
theorem t3_entry_residual_bit {c : BitVec 32} (h0 : 0 < c.toNat) (h4 : c.toNat < 4) :
    evalICmp .eq (BitVec.ofNat 64 c.toNat) (0 : BitVec 64) = (0 : BitVec 1) := by
  have h := t3_residual_test_zero h0 h4
  simpa only [t3_xtraiter_ofNat h4] using h

/-- **The traversal with the trip count.**  From the peeled entry at a count in
`0 < k < 4`, two control steps: the entry takes the residual edge, and the
residual block — its two `poison` `phi`s bound, its residue test refused — jumps
to the epilogue.  The reached state is the continuation, so the path the model
used to have to decline is a run whose cells are named. -/
theorem t3_traversal_counts_1_3 {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i")
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c))
    (h0 : 0 < c.toNat) (h4 : c.toNat < 4) (k : Nat) :
    runFuel calls (k + 2) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (t3ResidualEnv (t3EntryEnv env c) (BitVec.ofNat 64 c.toNat))
          { s with pc := "for.body.i.i566.i.i.epil",
                   pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) := by
  have hstep1 := t3_entry_step_residual (calls := calls) hpc hc h4
  have hstep2 := t3_poison_edge_step_zero (calls := calls)
    (env := t3EntryEnv env c)
    (s := { s with pc := "while.cond.preheader.i.i577.i.i.unr-lcssa",
                   pre := some "for.body.lr.ph.i.i564.i.i" })
    (x := BitVec.ofNat 64 c.toNat)
    rfl rfl (t3_entryEnv_xtraiter h4) (t3_entry_residual_bit h0 h4)
  rw [show k + 2 = (k + 1) + 1 from by omega]
  simp only [runFuel, hstep1, hstep2]

/-- The traversal's payload: in the state it reaches, both `poison` `phi` cells
hold the marker and neither has a value at a read. -/
theorem t3_traversal_markers (env : Env) (c : BitVec 32) (s : State) :
    lookupName (t3ResidualEnv (t3EntryEnv env c) (BitVec.ofNat 64 c.toNat))
        "%add4.i.i572.i.i.lcssa.ph" = some .poison ∧
    lookupName (t3ResidualEnv (t3EntryEnv env c) (BitVec.ofNat 64 c.toNat))
        "%shr.i.i574.i.i.lcssa.ph.off0" = some .poison ∧
    evalOperand
        (stateAt (t3ResidualEnv (t3EntryEnv env c) (BitVec.ofNat 64 c.toNat)) s)
        (.reg "%add4.i.i572.i.i.lcssa.ph") = none ∧
    evalOperand
        (stateAt (t3ResidualEnv (t3EntryEnv env c) (BitVec.ofNat 64 c.toNat)) s)
        (.reg "%shr.i.i574.i.i.lcssa.ph.off0") = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [t3ResidualEnv, t3EntryEnv, stateAt, lookupName, evalOperand]

/-! ### The window's copy: which limbs it keeps

`to_double` copies the lexeme's significant digits into a 768-byte array and
remembers one bit saying whether any digit past the window was nonzero.  The
model's `windowOf m E` is the same decomposition: `M = m / 10 ^ stkDrop m`, `S =
E + stkDrop m`, and the sticky bit is the dropped tail's nonzero-ness.  The tie
is three pieces — the retained digits as an integer (`copy_retained`), the
sticky bit (`copy_sticky`), and the loop's counters against the window's fields
(`copy_counters`) — and then the copy's taken edge `if.then31.i.i`, whose store
is where the digit the register carries lands in the array (`t3_copy_denote`).

`digVal` is the array read most significant first, which is the order the copy
writes (`dig[R] = d` at `R = 0, 1, …`) and the order `Decimal.digitsNat` folds a
lexeme. -/

open LeanLLVM.StrtodTier3

/-- The integer a run of decimal digits denotes, most significant first. -/
def digVal : List Nat → Nat
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + digVal ds

theorem digVal_append (ds es : List Nat) :
    digVal (ds ++ es) = digVal ds * 10 ^ es.length + digVal es := by
  induction ds with
  | nil => simp [digVal]
  | cons d ds ih =>
      show d * 10 ^ (ds ++ es).length + digVal (ds ++ es)
        = (d * 10 ^ ds.length + digVal ds) * 10 ^ es.length + digVal es
      rw [ih, List.length_append, Nat.pow_add, Nat.add_mul,
        show d * (10 ^ ds.length * 10 ^ es.length)
          = d * 10 ^ ds.length * 10 ^ es.length from (Nat.mul_assoc ..).symm
        , Nat.add_assoc]

/-- A digit list's value is below the decade its length names: no digit carries
into its neighbour. -/
theorem digVal_lt : ∀ {ds : List Nat}, (∀ d ∈ ds, d < 10) → digVal ds < 10 ^ ds.length
  | [], _ => by simp [digVal]
  | d :: ds, h => by
      have hd : d ≤ 9 := by have := h d (by simp); omega
      have hds : ∀ x ∈ ds, x < 10 := fun x hx => h x (by simp [hx])
      have hT : 0 < 10 ^ ds.length := Nat.pow_pos (by decide)
      have h1 : d * 10 ^ ds.length ≤ 9 * 10 ^ ds.length := Nat.mul_le_mul_right _ hd
      have h2 : digVal ds < 10 ^ ds.length := digVal_lt hds
      show d * 10 ^ ds.length + digVal ds < 10 ^ (ds.length + 1)
      rw [Nat.pow_succ]
      omega

/-- The same bound for a suffix: the digits the copy did not reach. -/
theorem digVal_lt_drop : ∀ (ds : List Nat) (k : Nat), (∀ x ∈ ds, x < 10) →
    digVal (ds.drop k) < 10 ^ (ds.drop k).length
  | [], _, _ => by simp [digVal]
  | _ :: _, 0, h => digVal_lt h
  | _ :: xs, k + 1, h => digVal_lt_drop xs k (fun y hy => h y (by simp [hy]))

/-- A suffix's digits are digits of the list. -/
theorem digits_lt_drop (ds : List Nat) (k : Nat) (h : ∀ x ∈ ds, x < 10) :
    ∀ x ∈ ds.drop k, x < 10 := by
  induction ds generalizing k with
  | nil => intro x hx; simp at hx
  | cons y ys ih =>
      intro x hx
      rcases k with _ | k
      · simp only [List.drop_zero] at hx
        exact h x hx
      · rw [List.drop_succ_cons] at hx
        exact ih k (fun z hz => h z (by simp [hz])) x hx

/-- A digit list is zero exactly when every digit is: the truncation the copy's
sticky bit replaces is invisible to the value only when there is nothing to
truncate. -/
theorem digVal_eq_zero : ∀ {ds : List Nat}, (∀ d ∈ ds, d < 10) →
    (digVal ds = 0 ↔ ∀ d ∈ ds, d = 0)
  | [], _ => by simp [digVal]
  | d :: ds, h => by
      have hds : ∀ x ∈ ds, x < 10 := fun x hx => h x (by simp [hx])
      have ih := digVal_eq_zero hds
      constructor
      · intro h0
        have h0' : d * 10 ^ ds.length + digVal ds = 0 := h0
        have hA : d * 10 ^ ds.length = 0 := by omega
        have hv : digVal ds = 0 := by omega
        have hT : 0 < 10 ^ ds.length := Nat.pow_pos (by decide)
        have hd0 : d = 0 := by
          rcases Nat.mul_eq_zero.mp hA with h' | h'
          · exact h'
          · omega
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hd0
        · exact ih.mp hv x hx'
      · intro hall
        show d * 10 ^ ds.length + digVal ds = 0
        have hd0 : d = 0 := hall d (by simp)
        have hv : digVal ds = 0 := ih.mpr (fun x hx => hall x (by simp [hx]))
        rw [hd0, hv, Nat.zero_mul, Nat.zero_add]

/-- A digit string whose leading digit is nonzero is as long as its decade: the
window's `ndig` is the copy's digit count. -/
theorem ndig_digVal {d : Nat} {ds : List Nat} (hd : 1 ≤ d)
    (hlt : ∀ x ∈ d :: ds, x < 10) :
    ndig (digVal (d :: ds)) = (d :: ds).length := by
  have hT : 0 < 10 ^ ds.length := Nat.pow_pos (by decide)
  have hlow : 10 ^ ds.length ≤ digVal (d :: ds) := by
    show 10 ^ ds.length ≤ d * 10 ^ ds.length + digVal ds
    have h1 : 1 * 10 ^ ds.length ≤ d * 10 ^ ds.length := Nat.mul_le_mul_right _ hd
    omega
  have hhigh : digVal (d :: ds) < 10 ^ (d :: ds).length := digVal_lt hlt
  have hpos : 0 < digVal (d :: ds) := by omega
  have hlen : (d :: ds).length = ds.length + 1 := rfl
  rw [hlen] at hhigh ⊢
  exact ndig_eq_of_bounds hpos (by rw [Nat.add_sub_cancel]; exact hlow) hhigh

/-- **The copy drops the right limbs.**  The digits the array keeps, read as one
integer, are the magnitude's quotient by `10 ^ stkDrop`: the window holds the
leading `stkDigits` digits and the drop is the low limbs. -/
theorem copy_retained {d : Nat} {ds : List Nat} (hd : 1 ≤ d)
    (hlt : ∀ x ∈ d :: ds, x < 10) :
    digVal ((d :: ds).take stkDigits)
      = digVal (d :: ds) / 10 ^ stkDrop (digVal (d :: ds)) := by
  have hnd := ndig_digVal hd hlt
  by_cases hle : (d :: ds).length ≤ stkDigits
  · have hdrop : stkDrop (digVal (d :: ds)) = 0 := by
      unfold stkDrop; rw [hnd]; omega
    rw [hdrop, Nat.pow_zero, Nat.div_one, List.take_of_length_le (by omega)]
  · have hlen : ((d :: ds).drop stkDigits).length = (d :: ds).length - stkDigits :=
      List.length_drop ..
    have hdrop : stkDrop (digVal (d :: ds)) = (d :: ds).length - stkDigits := by
      unfold stkDrop; rw [hnd]
    have hsplit : (d :: ds).take stkDigits ++ (d :: ds).drop stkDigits = d :: ds :=
      List.take_append_drop stkDigits (d :: ds)
    have hvalue : digVal (d :: ds)
        = digVal ((d :: ds).take stkDigits) * 10 ^ ((d :: ds).drop stkDigits).length
          + digVal ((d :: ds).drop stkDigits) := by
      conv_lhs => rw [← hsplit]
      rw [digVal_append]
    have htail : digVal ((d :: ds).drop stkDigits)
        < 10 ^ ((d :: ds).drop stkDigits).length :=
      digVal_lt_drop (d :: ds) stkDigits hlt
    rw [hdrop, hvalue]
    rw [hlen] at htail ⊢
    rw [Nat.add_comm _ (digVal ((d :: ds).drop stkDigits)),
      Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt htail,
      Nat.zero_add]

/-- **The sticky bit is the dropped tail.**  The copy's sticky bit is set exactly
when a digit past the window is nonzero, which is `windowOf`'s sticky: the
magnitude's remainder modulo `10 ^ stkDrop` is nonzero. -/
theorem copy_sticky {d : Nat} {ds : List Nat} (hd : 1 ≤ d)
    (hlt : ∀ x ∈ d :: ds, x < 10) :
    ((d :: ds).drop stkDigits).any (fun x => x != 0) = true ↔
      digVal (d :: ds) % 10 ^ stkDrop (digVal (d :: ds)) ≠ 0 := by
  have hnd := ndig_digVal hd hlt
  by_cases hle : (d :: ds).length ≤ stkDigits
  · have hdrop : stkDrop (digVal (d :: ds)) = 0 := by
      unfold stkDrop; rw [hnd]; omega
    have hnil : (d :: ds).drop stkDigits = [] := List.drop_eq_nil_of_le hle
    rw [hnil, hdrop, Nat.pow_zero, Nat.mod_one]
    simp
  · have hlen : ((d :: ds).drop stkDigits).length = (d :: ds).length - stkDigits :=
      List.length_drop ..
    have hdrop : stkDrop (digVal (d :: ds)) = (d :: ds).length - stkDigits := by
      unfold stkDrop; rw [hnd]
    have hsplit : (d :: ds).take stkDigits ++ (d :: ds).drop stkDigits = d :: ds :=
      List.take_append_drop stkDigits (d :: ds)
    have hvalue : digVal (d :: ds)
        = digVal ((d :: ds).take stkDigits) * 10 ^ ((d :: ds).drop stkDigits).length
          + digVal ((d :: ds).drop stkDigits) := by
      conv_lhs => rw [← hsplit]
      rw [digVal_append]
    have htail : digVal ((d :: ds).drop stkDigits)
        < 10 ^ ((d :: ds).drop stkDigits).length :=
      digVal_lt_drop (d :: ds) stkDigits hlt
    have hmod : digVal (d :: ds) % 10 ^ stkDrop (digVal (d :: ds))
        = digVal ((d :: ds).drop stkDigits) := by
      rw [hdrop, hvalue]
      rw [hlen] at htail ⊢
      rw [Nat.add_comm _ (digVal ((d :: ds).drop stkDigits)),
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htail]
    have htail_digits : ∀ x ∈ (d :: ds).drop stkDigits, x < 10 :=
      digits_lt_drop (d :: ds) stkDigits hlt
    have hany : ((d :: ds).drop stkDigits).any (fun x => x != 0) = true ↔
        ∃ x ∈ (d :: ds).drop stkDigits, x ≠ 0 := by
      rw [List.any_eq_true]
      simp
    rw [hany, hmod]
    constructor
    · rintro ⟨x, hx, hne⟩ hzero
      exact hne ((digVal_eq_zero htail_digits).mp hzero x hx)
    · intro hne
      by_contra hnany
      have hall : ∀ x ∈ (d :: ds).drop stkDigits, x = 0 := by
        intro x hx
        by_contra hx0
        exact hnany ⟨x, hx, hx0⟩
      exact hne ((digVal_eq_zero htail_digits).mpr hall)

/-- **The copy's counters are the window's fields.**  With the retained count
`R = min nsig stkDigits` and `nsig = T - lead` significant digits, the emitted
scale `S = exp10 - F + (nsig - R)` is `E + stkDrop` and the leading exponent
`f = (R - 1) + S` is `leadM`, which is the model's: the two clamps the body takes
at `f` are `roundMag`'s own. -/
theorem copy_counters {m nsig R T lead F : Nat} {exp10 : Int}
    (hnd : ndig m = nsig) (hnsig : nsig = T - lead)
    (hR : R = min nsig stkDigits) :
    stkDrop m = nsig - R ∧
    ((T - lead) - R : Nat) = stkDrop m ∧
    (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int))
      = (exp10 - (F : Int)) + (stkDrop m : Int) ∧
    ((R : Int) - 1 + (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int)))
      = leadM m (exp10 - (F : Int)) := by
  have hmin : nsig - min nsig stkDigits = nsig - stkDigits := by
    by_cases h : nsig ≤ stkDigits
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right (by omega : stkDigits ≤ nsig)]
  have hdrop : stkDrop m = nsig - R := by
    unfold stkDrop
    rw [hnd, hR, hmin]
  refine ⟨hdrop, by rw [← hnsig, hdrop], by rw [← hnsig, hdrop], ?_⟩
  rw [← hnsig]
  unfold leadM
  rw [hnd]
  have hsum : (R : Int) + ((nsig - R : Nat) : Int) = (nsig : Int) := by omega
  omega

/-- The retained array is `windowOf`'s `M`, in the model's own name. -/
theorem copy_retained_window {d : Nat} {ds : List Nat} (hd : 1 ≤ d) (E : Int)
    (hlt : ∀ x ∈ d :: ds, x < 10) :
    digVal ((d :: ds).take stkDigits) = (windowOf (digVal (d :: ds)) E).M := by
  rw [windowOf_M]
  exact copy_retained hd hlt

/-- The copy's sticky bit is `windowOf`'s, in the model's own name. -/
theorem copy_sticky_window {d : Nat} {ds : List Nat} (hd : 1 ≤ d) (E : Int)
    (hlt : ∀ x ∈ d :: ds, x < 10) :
    ((d :: ds).drop stkDigits).any (fun x => x != 0)
      = (windowOf (digVal (d :: ds)) E).sticky := by
  apply Bool.eq_iff_iff.mpr
  rw [copy_sticky hd hlt, windowOf_sticky_iff]

/-- The emitted scale is `windowOf`'s `S`. -/
theorem copy_S_window {m nsig R T lead F : Nat} {exp10 : Int}
    (hnd : ndig m = nsig) (hnsig : nsig = T - lead)
    (hR : R = min nsig stkDigits) :
    (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int))
      = (windowOf m (exp10 - (F : Int))).S := by
  rw [windowOf_S]
  exact (copy_counters hnd hnsig hR).2.2.1

/-- The emitted leading exponent is `windowOf`'s `lead`, so the body's two
clamps at `f` are the model's. -/
theorem copy_lead_window {m nsig R T lead F : Nat} {exp10 : Int} (hm : 0 < m)
    (hnd : ndig m = nsig) (hnsig : nsig = T - lead)
    (hR : R = min nsig stkDigits) :
    ((R : Int) - 1 + (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int)))
      = (windowOf m (exp10 - (F : Int))).lead := by
  rw [window_lead hm]
  simpa only [leadM] using (copy_counters hnd hnsig hR).2.2.2

/-! ### The copy's taken edge

`if.then31.i.i` is where the array is written: it increments the retained count,
forms `dig + R` with a `getelementptr i8`, stores the digit there, and tests
`topn < 19`.  The step below is that block at its pin, so the register the loop
carries is the byte the store lands and the array `digVal` reads is the one the
copy builds. -/

/-- The block's instructions, from its `findBlock` pin. -/
def t3CopyInstrs : List Instr :=
  [Instr.binop "%inc32.i.i" (BinOp.add) 64 (Operand.reg "%R.0724.ph.i.ph.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.gep "%arrayidx33.i.i" (Ty.int 8) (Operand.reg "%dig.i.i")
     (Operand.reg "%R.0724.ph.i.ph.i"),
   Instr.store (Ty.int 8) (Operand.reg "%.lcssa277.i") (Operand.reg "%arrayidx33.i.i"),
   Instr.icmp "%cmp34.i.i" (IPred.ult) 64 (Operand.reg "%topn.0719.ph.i.ph.i")
     (Operand.imm (Const.int 64 0x0000000000000013#64))]

theorem t3_findBlock_copy :
    numFastBody.findBlock "if.then31.i.i" =
      some ⟨"if.then31.i.i", t3CopyInstrs,
        Term.condbr (Operand.reg "%cmp34.i.i") "if.then36.i.i" "for.inc.i.i"⟩ := by
  simpa only [t3CopyInstrs] using numFast_findBlock_if_then31_i_i

/-- The environment the block leaves: the incremented count, the address the
digit is written at, and the `topn < 19` test. -/
def t3CopyEnv (env : Env) (topn : BitVec 64) (a : Nat) (R : BitVec 64) : Env :=
  ("%cmp34.i.i", .int 1 (evalICmp .ult topn 0x13#64)) ::
  ("%arrayidx33.i.i", .ptr (a + (R.signExtend 64).toNat)) ::
  ("%inc32.i.i", .int 64 (R + 1#64)) :: env

/-- A one-byte store: the digit's byte at the address the operand carries. -/
theorem step_store8 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 8} {a : Nat}
    (hv : lookupName env v = some (.int 8 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 8) (.reg v) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hdiv : (8 + 7) / 8 = 1 := by decide
  simp only [evalInstr, evalOperand, stateAt, hv, hp, storeValue, hdiv, ite_true]

/-- The state the copy's edge leaves: the environment `t3CopyEnv` and the byte
the store wrote at `dig + R`. -/
def t3CopyState (env : Env) (topn : BitVec 64) (a : Nat) (R : BitVec 64)
    (d : BitVec 8) (s : State) : State :=
  { stateAt (t3CopyEnv env topn a R) s with
      mem := writeBytes s.mem (a + (R.signExtend 64).toNat) (natToBytes d.toNat 1) }

/-- **The copy's store.**  `if.then31.i.i` at its pin: the digit the register
carries is the byte the store writes, at `dig + R`, and the block's test is
`topn < 19`.  This is the block whose store builds the array the accounting
above reads. -/
theorem t3_copy_denote {calls : Calls} {env : Env} {s : State}
    {R topn : BitVec 64} {d : BitVec 8} {a : Nat}
    (hdig : lookupName env "%dig.i.i" = some (.ptr a))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hval : lookupName env "%.lcssa277.i" = some (.int 8 d))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (hpos : (R.signExtend 64).toNat < 2 ^ 63) :
    denoteCode calls t3CopyInstrs (stateAt env s) =
      some (t3CopyState env topn a R d s) := by
  unfold t3CopyInstrs
  rw [denoteCode_cons_of _ _ _ _ _
    (step_add_imm calls env s "%inc32.i.i" "%R.0724.ph.i.ph.i" hR)]
  rw [denoteCode_cons_of _ _ _ _ _
    (step_gep8_reg calls _ s "%arrayidx33.i.i" "%dig.i.i" "%R.0724.ph.i.ph.i"
      (lookupName_cons_tail (by decide) hdig)
      (lookupName_cons_tail (by decide) hR) hpos)]
  rw [denoteCode_cons_of _ _ _ _ _
    (step_store8 calls _ s "%.lcssa277.i" "%arrayidx33.i.i"
      (lookupName_cons_tail (by decide)
        (lookupName_cons_tail (by decide) hval)) (lookupName_cons_self ..))]
  rw [denoteCode_cons_of _ _ _ _ _
    (step_icmp_ult_imm calls _ _ "%cmp34.i.i" "%topn.0719.ph.i.ph.i"
      (lookupName_cons_tail (by decide)
        (lookupName_cons_tail (by decide) htopn)))]
  simp only [denoteCode_nil, t3CopyEnv, t3CopyState, stateAt]

/-! ### The epilogue chain: `for.body.i.i566.i.i.epil`

The traversal hands the residual path to the peeled nest's epilogue.  The block
is the copy's last group: its three carried `phi`s (the index, the carry and the
residue counter), the table's row read at `%pow.i.i + %indvars`, the widen and the
`10 ^ 19` multiply, the carry's addition at `i128`, the low word's store, the high
word's `lshr` by sixty-four, the two increments, and the residue test.  It is the
region's only block that works at `i128`, so the three operations it needs beyond
the existing chain steps — `mul` with an immediate, `add` of two registers, and
`lshr` with an immediate — are stated width-generically here, and the block is
then one chain at its pin, with both of its successors.

`t3PowConst` is `10 ^ 19`, the `NUMF_EL1_P10` row the copy reads past the
nineteen it retains; the shift is the `i128` sum's high word. -/

/-- `10 ^ 19` at `i128`: the epilogue's multiplier, the table's twentieth row. -/
def t3PowConst : BitVec 128 := 0x8ac7230489e80000#128

/-- The multiplier is the table's row, at the width the epilogue's multiply
reads. -/
theorem t3PowConst_eq : t3PowConst = BitVec.ofNat 128 (10 ^ 19) := by decide

/-- `%d = mul iW %a, <c>`, at any width. -/
theorem step_mul_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .mul w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x * c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (r := (x * c).toNat)
      (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The chain step for `mul iW %a, <c>`. -/
theorem denoteCode_mul_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .mul w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x * c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_mul_imm_w calls env s d a w ha)]

/-- `%d = add iW %a, %b`, at any width. -/
theorem step_add_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x + y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (r := (x + y).toNat)
      (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The chain step for `add iW %a, %b`. -/
theorem denoteCode_add_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_add_reg_w calls env s d a b w ha hb)]

/-- `%d = lshr iW %a, <c>`, at any width. -/
theorem step_lshr_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .lshr w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x >>> c.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (r := (x >>> c.toNat).toNat)
      (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The chain step for `lshr iW %a, <c>`. -/
theorem denoteCode_lshr_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .lshr w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x >>> c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_lshr_imm_w calls env s d a w ha)]

/-- The epilogue's `i128` product: the widened table row times `10 ^ 19`. -/
def t3EpilProd (w : BitVec 64) : BitVec 128 := BitVec.ofNat 128 w.toNat * t3PowConst

/-- The epilogue's `i128` sum: the product plus the carried word. -/
def t3EpilSum (w : BitVec 64) (carry : BitVec 128) : BitVec 128 := t3EpilProd w + carry

/-- The block's leading `phi` run, from its pin. -/
def t3EpilPhis : List Instr :=
  [Instr.phi "%indvars.iv.i.i567.i.i.epil" (Ty.int 64)
     [("for.body.i.i566.i.i.epil", (Operand.reg "%indvars.iv.next.i.i575.i.i.epil")),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa",
        (Operand.reg "%indvars.iv.i.i567.i.i.unr"))],
   Instr.phi "%carry.029.i.i568.i.i.epil" (Ty.int 128)
     [("for.body.i.i566.i.i.epil", (Operand.reg "%shr.i.i574.i.i.epil")),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa",
        (Operand.reg "%carry.029.i.i568.i.i.unr"))],
   Instr.phi "%epil.iter1084" (Ty.int 64)
     [("for.body.i.i566.i.i.epil", (Operand.reg "%epil.iter1084.next")),
      ("while.cond.preheader.i.i577.i.i.unr-lcssa",
        (Operand.imm (Const.int 64 0x0000000000000000#64)))]]

/-- The block's instructions: its `phi` run, then the table read, the `i128`
arithmetic, the store, the two increments and the residue test. -/
def t3EpilInstrs : List Instr :=
  t3EpilPhis ++
    [Instr.gep "%arrayidx.i.i569.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i")
       (Operand.reg "%indvars.iv.i.i567.i.i.epil"),
     Instr.load "%102" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.epil"),
     Instr.zext "%conv2.i.i570.i.i.epil" 64 128 (Operand.reg "%102"),
     Instr.binop "%mul.i.i571.i.i.epil" (BinOp.mul) 128
       (Operand.reg "%conv2.i.i570.i.i.epil")
       (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
     Instr.binop "%add4.i.i572.i.i.epil" (BinOp.add) 128
       (Operand.reg "%mul.i.i571.i.i.epil")
       (Operand.reg "%carry.029.i.i568.i.i.epil"),
     Instr.trunc "%conv5.i.i573.i.i.epil" 128 64 (Operand.reg "%add4.i.i572.i.i.epil"),
     Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.epil")
       (Operand.reg "%arrayidx.i.i569.i.i.epil"),
     Instr.binop "%shr.i.i574.i.i.epil" (BinOp.lshr) 128
       (Operand.reg "%add4.i.i572.i.i.epil")
       (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
     Instr.binop "%indvars.iv.next.i.i575.i.i.epil" (BinOp.add) 64
       (Operand.reg "%indvars.iv.i.i567.i.i.epil")
       (Operand.imm (Const.int 64 0x0000000000000001#64)),
     Instr.binop "%epil.iter1084.next" (BinOp.add) 64
       (Operand.reg "%epil.iter1084")
       (Operand.imm (Const.int 64 0x0000000000000001#64)),
     Instr.icmp "%epil.iter1084.cmp.not" (IPred.eq) 64
       (Operand.reg "%epil.iter1084.next") (Operand.reg "%xtraiter1083")]

theorem t3_findBlock_epil :
    numFastBody.findBlock "for.body.i.i566.i.i.epil" =
      some ⟨"for.body.i.i566.i.i.epil", t3EpilInstrs,
        Term.condbr (Operand.reg "%epil.iter1084.cmp.not")
          "while.cond.preheader.i.i577.i.i.epilog-lcssa" "for.body.i.i566.i.i.epil"⟩ := by
  simpa only [t3EpilInstrs, t3EpilPhis, List.cons_append, List.nil_append] using
    numFast_findBlock_for_body_i_i566_i_i_epil

/-- The environment the block leaves: the three carried `phi`s, the table
address, the widened row, its product and sum, the stored low word and the
shifted high word, the two increments and the residue test. -/
def t3EpilEnv (env : Env) (addr : Nat) (w : BitVec 64) (iv : BitVec 64)
    (carry : BitVec 128) (iter : BitVec 64) (xt : BitVec 64) : Env :=
  ("%epil.iter1084.cmp.not", .int 1 (evalICmp .eq (iter + 0x1#64) xt)) ::
  ("%epil.iter1084.next", .int 64 (iter + 0x1#64)) ::
  ("%indvars.iv.next.i.i575.i.i.epil", .int 64 (iv + 0x1#64)) ::
  ("%shr.i.i574.i.i.epil", .int 128
    (t3EpilSum w carry >>> (0x00000000000000000000000000000040#128).toNat)) ::
  ("%conv5.i.i573.i.i.epil", .int 64
    (BitVec.ofNat 64 ((t3EpilSum w carry).toNat % 2 ^ 64))) ::
  ("%add4.i.i572.i.i.epil", .int 128 (t3EpilSum w carry)) ::
  ("%mul.i.i571.i.i.epil", .int 128 (t3EpilProd w)) ::
  ("%conv2.i.i570.i.i.epil", .int 128 (BitVec.ofNat 128 w.toNat)) ::
  ("%102", .int 64 w) ::
  ("%arrayidx.i.i569.i.i.epil", .ptr (addr + (iv.signExtend 64).toNat * 8)) ::
  ("%epil.iter1084", .int 64 iter) ::
  ("%carry.029.i.i568.i.i.epil", .int 128 carry) ::
  ("%indvars.iv.i.i567.i.i.epil", .int 64 iv) :: env

/-- The state the block leaves: the environment above and the low word written
at the table row's address. -/
def t3EpilState (env : Env) (addr : Nat) (w : BitVec 64) (iv : BitVec 64)
    (carry : BitVec 128) (iter : BitVec 64) (xt : BitVec 64) (s : State) : State :=
  { stateAt (t3EpilEnv env addr w iv carry iter xt) s with
      mem := writeBytes s.mem (addr + (iv.signExtend 64).toNat * 8)
        (natToBytes (BitVec.ofNat 64 ((t3EpilSum w carry).toNat % 2 ^ 64)).toNat 8) }

/-- **The epilogue's chain from the traversal's edge.**  At the entry edge the
three `phi`s take the traversal's cells and the residue counter's zero, and the
block runs to its test: the row read, the widen, the `10 ^ 19` multiply, the
carry's addition, the low word's store, the high word's shift, the increments. -/
theorem t3_epil_denote {calls : Calls} {env : Env} {s : State}
    {addr : Nat} {w : BitVec 64} {iv : BitVec 64} {carry : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some "while.cond.preheader.i.i577.i.i.unr-lcssa")
    (hp : lookupName env "%pow.i.i" = some (.ptr addr))
    (hiv : lookupName env "%indvars.iv.i.i567.i.i.unr" = some (.int 64 iv))
    (hcarry : lookupName env "%carry.029.i.i568.i.i.unr" = some (.int 128 carry))
    (hxt : lookupName env "%xtraiter1083" = some (.int 64 xt))
    (hpos : (iv.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (addr + (iv.signExtend 64).toNat * 8) 8
      = some (natToBytes w.toNat 8)) :
    denoteCode calls t3EpilInstrs (stateAt env s) =
      some (t3EpilState env addr w iv carry (0x0000000000000000#64) xt s) := by
  unfold t3EpilInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%indvars.iv.i.i567.i.i.unr" _ hiv
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%carry.029.i.i568.i.i.unr" _ hcarry
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_lit_of _ 64 (0x0000000000000000#64)
  rw [NumFastTier1.denoteCode_gep64_reg calls _ _ "%arrayidx.i.i569.i.i.epil" "%pow.i.i"
    "%indvars.iv.i.i567.i.i.epil" (by block_lk) (by block_lk) hpos _]
  rw [denoteCode_load64 calls _ _ "%102" "%arrayidx.i.i569.i.i.epil"
    (by block_lk) hread _]
  rw [denoteCode_zext calls _ _ "%conv2.i.i570.i.i.epil" "%102" 64 128
    (by block_lk) _]
  rw [denoteCode_mul_imm_w calls _ _ "%mul.i.i571.i.i.epil"
    "%conv2.i.i570.i.i.epil" 128 (by block_lk) _]
  rw [denoteCode_add_reg_w calls _ _ "%add4.i.i572.i.i.epil" "%mul.i.i571.i.i.epil"
    "%carry.029.i.i568.i.i.epil" 128 (by block_lk) (by block_lk) _]
  rw [denoteCode_trunc calls _ _ "%conv5.i.i573.i.i.epil" "%add4.i.i572.i.i.epil"
    128 64 (by block_lk) _]
  rw [denoteCode_store64 calls _ _ "%conv5.i.i573.i.i.epil" "%arrayidx.i.i569.i.i.epil"
    (by block_lk) (by block_lk) _]
  rw [denoteCode_lshr_imm_w calls _ _ "%shr.i.i574.i.i.epil" "%add4.i.i572.i.i.epil"
    128 (by block_lk) _]
  rw [JsonScanLane.denoteCode_add_imm_w calls _ _ "%indvars.iv.next.i.i575.i.i.epil"
    "%indvars.iv.i.i567.i.i.epil" 64 (by block_lk) _]
  rw [JsonScanLane.denoteCode_add_imm_w calls _ _ "%epil.iter1084.next" "%epil.iter1084"
    64 (by block_lk) _]
  rw [BlockEval.denoteCode_icmp_eq_reg calls _ _ "%epil.iter1084.cmp.not"
    "%epil.iter1084.next" "%xtraiter1083" (by block_lk) (by block_lk) _]
  simp only [denoteCode_nil, stateAt, runCells, t3EpilState, t3EpilEnv, t3EpilProd,
    t3EpilSum, t3PowConst]

/-- The epilogue's step to its exit: the residue counter reached the remainder,
so the path leaves for `while.cond.preheader.i.i577.i.i.epilog-lcssa`. -/
theorem t3_epil_step_lcssa {calls : Calls} {env : Env} {s : State}
    {addr : Nat} {w : BitVec 64} {iv : BitVec 64} {carry : BitVec 128}
    {iter : BitVec 64} {xt : BitVec 64}
    (hpc : s.pc = "for.body.i.i566.i.i.epil")
    (hden : denoteCode calls t3EpilInstrs (stateAt env s) =
      some (t3EpilState env addr w iv carry iter xt s))
    (hbit : evalICmp .eq (iter + 0x1#64) xt = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (t3EpilState env addr w iv carry iter xt
        { s with pc := "while.cond.preheader.i.i577.i.i.epilog-lcssa",
                 pre := some "for.body.i.i566.i.i.epil" }) := by
  refine numFast_step_at (s' := t3EpilState env addr w iv carry iter xt s)
    (b := ⟨"for.body.i.i566.i.i.epil", t3EpilInstrs,
      Term.condbr (Operand.reg "%epil.iter1084.cmp.not")
        "while.cond.preheader.i.i577.i.i.epilog-lcssa" "for.body.i.i566.i.i.epil"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_findBlock_epil
  · exact hden
  · have hlk : lookupName (t3EpilEnv env addr w iv carry iter xt) "%epil.iter1084.cmp.not"
        = some (.int 1 (evalICmp .eq (iter + 0x1#64) xt)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%epil.iter1084.cmp.not" _ _
      hlk hbit]
    simp only [t3EpilState, stateAt, hpc]

/-- The epilogue's step back to itself: the residue counter is short of the
remainder, so the next group is the same block at the incremented counter. -/
theorem t3_epil_step_self {calls : Calls} {env : Env} {s : State}
    {addr : Nat} {w : BitVec 64} {iv : BitVec 64} {carry : BitVec 128}
    {iter : BitVec 64} {xt : BitVec 64}
    (hpc : s.pc = "for.body.i.i566.i.i.epil")
    (hden : denoteCode calls t3EpilInstrs (stateAt env s) =
      some (t3EpilState env addr w iv carry iter xt s))
    (hbit : evalICmp .eq (iter + 0x1#64) xt = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (t3EpilState env addr w iv carry iter xt
        { s with pc := "for.body.i.i566.i.i.epil",
                 pre := some "for.body.i.i566.i.i.epil" }) := by
  refine numFast_step_at (s' := t3EpilState env addr w iv carry iter xt s)
    (b := ⟨"for.body.i.i566.i.i.epil", t3EpilInstrs,
      Term.condbr (Operand.reg "%epil.iter1084.cmp.not")
        "while.cond.preheader.i.i577.i.i.epilog-lcssa" "for.body.i.i566.i.i.epil"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_findBlock_epil
  · exact hden
  · have hlk : lookupName (t3EpilEnv env addr w iv carry iter xt) "%epil.iter1084.cmp.not"
        = some (.int 1 (evalICmp .eq (iter + 0x1#64) xt)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%epil.iter1084.cmp.not" _ _
      hlk hbit]
    simp only [t3EpilState, stateAt, hpc]

/-! ### The proximity estimate at the tree's own rounding

The emitted starting approximation is `top * 10 ^ e10`, at most two `fmul`/`fdiv`
of a table row each, and every one of those is `packMag ∘ roundMag`
(`JsonStage2NumFastTier1.fmulBits_pack`, `fdivBits_pack`): one nearest rounding
of an exact rational, not a platform operation.  So the error the walk starts
with is a lattice step per operation, and a boundary it compares — the candidate
or a midpoint, at most two patterns from the approximation — is within two ulps
of the approximation.  The arithmetic below turns that into the premise `stkCmp`
and `shift_of_near` take, `V ≤ 2 * B`, so the scale hypothesis is a statement
about `packMag ∘ roundMag`.

`t3RoundStep` is the lattice step at the exact value: one tick in the subnormal
region, where the lattice is the integers and `ulp` is zero by its own
definition, and the binade's ulp above it.  `roundMag_dist_le_step` is the
per-rounding bound — one step, whichever branch `roundMag` takes; `proximity_scale`
is the two-step composition; `valLeqBoundary_iff_cross` reads the tier module's
boundary predicate as the cleared comparison; and `t3_scale_of_ulp` is the
composed conclusion at `valLeqBoundary m E (2 * J) eB`, which is exactly what
`shift_of_near` consumes. -/

/-- The lattice step at the exact value `P / d`: one tick below the subnormal
threshold, the binade's ulp above it. -/
def t3RoundStep (P d : Nat) : Nat := if P < d * 2 ^ 52 then 1 else ulp P d

/-- The rounded magnitude is a code of the format. -/
theorem roundMag_isMag {P d : Nat} (hd : 0 < d) (hno : ¬ overflowTicks * d ≤ P)
    {c : Code} (hc : roundMag P d = .fin c) : c.IsMag := by
  unfold roundMag at hc
  rw [ite_eq_right hno] at hc
  by_cases hsub : P < d * 2 ^ 52
  · rw [ite_eq_left hsub] at hc
    injection hc with hce
    rw [← hce]
    exact subCode_isMag hd hsub
  · rw [ite_eq_right hsub] at hc
    injection hc with hce
    rw [← hce]
    exact normalCode_isMag hd hno hsub

/-- The lattice point below the exact value, as the cleared product. -/
theorem lo_mul {P d : Nat} :
    lo P d * d = P / (d * ulp P d) * (d * ulp P d) := by
  show P / (d * ulp P d) * ulp P d * d = _
  rw [Nat.mul_assoc, Nat.mul_comm (ulp P d) d]

/-- The lattice point above the exact value, as the cleared product. -/
theorem hi_mul {P d : Nat} :
    hi P d * d = P / (d * ulp P d) * (d * ulp P d) + d * ulp P d := by
  show (P / (d * ulp P d) + 1) * ulp P d * d = _
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_comm (ulp P d) d]

/-- The lattice point below is within one ulp. -/
theorem dist_lo_le {P d : Nat} (hd : 0 < d) (_hB : 52 ≤ binade P d) :
    distNum P d (lo P d) ≤ d * ulp P d := by
  have hpos : 0 < d * ulp P d := Nat.mul_pos hd (two_pow_pos _)
  have hmod : P % (d * ulp P d) < d * ulp P d := Nat.mod_lt P hpos
  have hdem : P / (d * ulp P d) * (d * ulp P d) + P % (d * ulp P d) = P := by
    rw [Nat.mul_comm (P / (d * ulp P d)) (d * ulp P d)]
    exact Nat.div_add_mod P (d * ulp P d)
  have hle : lo P d * d ≤ P := by
    rw [lo_mul]; exact Nat.div_mul_le_self P (d * ulp P d)
  simp only [distNum, hle, reduceIte]
  rw [lo_mul]
  omega

/-- The lattice point above is within one ulp. -/
theorem dist_hi_le {P d : Nat} (hd : 0 < d) (_hB : 52 ≤ binade P d) :
    distNum P d (hi P d) ≤ d * ulp P d := by
  have hpos : 0 < d * ulp P d := Nat.mul_pos hd (two_pow_pos _)
  have hmod : P % (d * ulp P d) < d * ulp P d := Nat.mod_lt P hpos
  have hdem : P / (d * ulp P d) * (d * ulp P d) + P % (d * ulp P d) = P := by
    rw [Nat.mul_comm (P / (d * ulp P d)) (d * ulp P d)]
    exact Nat.div_add_mod P (d * ulp P d)
  have hgt : ¬ hi P d * d ≤ P := by
    rw [hi_mul]; omega
  simp only [distNum, hgt, reduceIte]
  rw [hi_mul]
  omega

/-- **One rounding is at most one lattice step.**  `roundMag`'s result is within
a step of the exact value `P / d`, in either branch: the subnormal lattice is the
integers and the normal one is the binade's.  This is the per-operation error the
emitted approximation's fold accumulates. -/
theorem roundMag_dist_le_step {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) {c : Code} (hc : roundMag P d = .fin c) :
    distNum P d c.ticks ≤ d * t3RoundStep P d := by
  unfold roundMag at hc
  rw [ite_eq_right hno] at hc
  by_cases hsub : P < d * 2 ^ 52
  · rw [ite_eq_left hsub] at hc
    injection hc with hce
    rw [← hce]
    have hstep : t3RoundStep P d = 1 := by unfold t3RoundStep; rw [ite_eq_left hsub]
    rw [hstep, Nat.mul_one]
    rcases sub_ticks (P := P) (d := d) with h | h
    · rw [h]
      have hle : P / d * d ≤ P := Nat.div_mul_le_self P d
      have hdem : P / d * d + P % d = P := by
        rw [Nat.mul_comm (P / d) d]; exact Nat.div_add_mod P d
      have hmod : P % d < d := Nat.mod_lt P hd
      simp only [distNum, hle, reduceIte]
      omega
    · rw [h]
      have hdem : P / d * d + P % d = P := by
        rw [Nat.mul_comm (P / d) d]; exact Nat.div_add_mod P d
      have hmod : P % d < d := Nat.mod_lt P hd
      have hexp : (P / d + 1) * d = P / d * d + d := by rw [Nat.add_mul, Nat.one_mul]
      have hgt : ¬ (P / d + 1) * d ≤ P := by rw [hexp]; omega
      simp only [distNum, hgt, reduceIte]
      rw [hexp]
      omega
  · rw [ite_eq_right hsub] at hc
    injection hc with hce
    rw [← hce]
    obtain ⟨hB, -, -, -⟩ := binade_facts hd hno hsub
    have hstep : t3RoundStep P d = ulp P d := by unfold t3RoundStep; rw [ite_eq_right hsub]
    rw [hstep]
    rcases normal_ticks hB with h | h <;> rw [h]
    · exact dist_lo_le hd hB
    · exact dist_hi_le hd hB

/-- **The product's single rounding.**  At two exact nonnegative operands the
product's bits are `packMag` of one rounding, and that rounding is within one
lattice step of the exact product: the error of one emitted `fmul` is a step of
the tree's own `roundMag`. -/
theorem fmulBits_dist_le_step {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag)
    (hno : ¬ overflowTicks * 2 ^ 1074 ≤ c₁.ticks * c₂.ticks)
    {c : Code} (hc : roundMag (c₁.ticks * c₂.ticks) (2 ^ 1074) = .fin c) :
    F64.magTicks (F64.ofBits
        (fmulBits (packMag (.fin c₁) false) (packMag (.fin c₂) false))) = c.ticks ∧
      distNum (c₁.ticks * c₂.ticks) (2 ^ 1074) c.ticks
        ≤ 2 ^ 1074 * t3RoundStep (c₁.ticks * c₂.ticks) (2 ^ 1074) := by
  have hd : 0 < 2 ^ 1074 := Nat.pow_pos (by decide)
  refine ⟨?_, roundMag_dist_le_step hd hno hc⟩
  rw [NumFastTier1.fmulBits_pack h₁ h₂, hc,
    NumFastTier1.magTicks_ofBits_packMag_false (roundMag_isMag hd hno hc)]

/-- **The quotient's single rounding.**  The same for one emitted `fdiv`. -/
theorem fdivBits_dist_le_step {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag)
    (hpos : 0 < c₂.ticks) (hno : ¬ overflowTicks * c₂.ticks ≤ c₁.ticks * 2 ^ 1074)
    {c : Code} (hc : roundMag (c₁.ticks * 2 ^ 1074) c₂.ticks = .fin c) :
    F64.magTicks (F64.ofBits
        (fdivBits (packMag (.fin c₁) false) (packMag (.fin c₂) false))) = c.ticks ∧
      distNum (c₁.ticks * 2 ^ 1074) c₂.ticks c.ticks
        ≤ c₂.ticks * t3RoundStep (c₁.ticks * 2 ^ 1074) c₂.ticks := by
  refine ⟨?_, roundMag_dist_le_step hpos hno hc⟩
  rw [NumFastTier1.fdivBits_pack h₁ h₂ hpos, hc,
    NumFastTier1.magTicks_ofBits_packMag_false (roundMag_isMag hpos hno hc)]

/-- **The two-step proximity arithmetic.**  A value within two lattice steps of
the approximation, and a boundary within two of it, with the approximation at
least six steps above the subnormal floor, puts the boundary at or above half the
value: `V ≤ 2 * B`.  The constants are the walk's own — it compares the candidate
and one midpoint, at most two patterns from the approximation.

`6 * u ≤ w` is the slack the arithmetic needs, and it is nearly free: in the
subnormal region the lattice step is one tick, so it excludes only a magnitude
below six units of `2 ^ -1074`, where the candidates are the ladder's first few
integers and `roundMag`'s own subnormal branch decides — the band is named here
rather than assumed away. -/
theorem proximity_scale {V wS B uS : Nat} (hV : V ≤ wS + 2 * uS)
    (hB : wS ≤ B + 2 * uS) (hw : 6 * uS ≤ wS) : V ≤ 2 * B := by
  omega

/-- The value `m * 10 ^ E`'s numerator over `10 ^ |E|`. -/
def valNum (m : Nat) (E : Int) : Nat := m * 10 ^ E.toNat

/-- The denominator `10 ^ |E|`, one for a nonnegative exponent. -/
def tenDen (E : Int) : Nat := if 0 ≤ E then 1 else 10 ^ E.natAbs

/-- The boundary `J * 2 ^ eB`'s numerator over `2 ^ |eB|`. -/
def boundNum (J : Nat) (eB : Int) : Nat := J * 2 ^ eB.toNat

/-- The denominator `2 ^ |eB|`, one for a nonnegative exponent. -/
def twoDen (eB : Int) : Nat := if 0 ≤ eB then 1 else 2 ^ eB.natAbs

theorem tenDen_pos (E : Int) : 0 < tenDen E := by
  unfold tenDen
  split
  · exact Nat.one_pos
  · exact Nat.pow_pos (by decide)

theorem twoDen_pos (eB : Int) : 0 < twoDen eB := by
  unfold twoDen
  split
  · exact Nat.one_pos
  · exact Nat.pow_pos (by decide)

/-- `a < b ∨ a = b` is `a ≤ b` at the naturals, stated as a rewrite. -/
theorem lt_or_eq_iff_le {a b : Nat} : (a < b ∨ a = b) ↔ a ≤ b :=
  ⟨fun h => h.elim Nat.le_of_lt (fun he => he.le), Nat.lt_or_eq_of_le⟩

/-- **The tier module's boundary predicate is the cleared comparison.**  Each of
`valLtBoundary`'s four sign cases is the cross-multiplied form at the same
coordinate, so `V ≤ B` is `valNum * twoDen ≤ boundNum * tenDen` exactly. -/
theorem valLeqBoundary_iff_cross {m : Nat} {E : Int} {J : Nat} {eB : Int} :
    valLeqBoundary m E J eB ↔ valNum m E * twoDen eB ≤ boundNum J eB * tenDen E := by
  by_cases hE : 0 ≤ E <;> by_cases heB : 0 ≤ eB
  · simp only [valLeqBoundary, valLtBoundary, valEqBoundary, valNum, boundNum,
      tenDen, twoDen, hE, heB, reduceIte, Nat.mul_one]
    exact lt_or_eq_iff_le
  · have hto : eB.toNat = 0 := Int.toNat_of_nonpos (by omega)
    have hden : (0 : Int) ≤ eB → False := by omega
    simp only [valLeqBoundary, valLtBoundary, valEqBoundary, valNum, boundNum,
      tenDen, twoDen, hE, heB, reduceIte, hto, Nat.pow_zero, Nat.mul_one]
    exact lt_or_eq_iff_le
  · have hto : E.toNat = 0 := Int.toNat_of_nonpos (by omega)
    simp only [valLeqBoundary, valLtBoundary, valEqBoundary, valNum, boundNum,
      tenDen, twoDen, hE, heB, reduceIte, hto, Nat.pow_zero, Nat.mul_one]
    exact lt_or_eq_iff_le
  · have htoE : E.toNat = 0 := Int.toNat_of_nonpos (by omega)
    have htoB : eB.toNat = 0 := Int.toNat_of_nonpos (by omega)
    simp only [valLeqBoundary, valLtBoundary, valEqBoundary, valNum, boundNum,
      tenDen, twoDen, hE, heB, reduceIte, htoE, htoB, Nat.pow_zero, Nat.mul_one]
    exact lt_or_eq_iff_le

/-- **The scale hypothesis from the tree's own rounding.**  At the common scale
`tenDen E * twoDen eB` the value is within two lattice steps of the emitted
approximation and the boundary within two of the approximation; that is the
two-ulp proximity estimate, and it gives `V ≤ 2 * B`, which is
`valLeqBoundary m E (2 * J) eB`.  `shift_of_near` then reads it as the right
shift the sticky branch performs. -/
theorem t3_scale_of_ulp {m : Nat} {E : Int} {J : Nat} {eB : Int} {w u : Nat}
    (hm : 0 < m) (hJ : J < 2 ^ 54) (heB : -1075 ≤ eB) (hlead : leadM m E ≤ 308)
    (hV : valNum m E * twoDen eB
      ≤ w * (tenDen E * twoDen eB) + 2 * (u * (tenDen E * twoDen eB)))
    (hB : w * (tenDen E * twoDen eB)
      ≤ boundNum J eB * tenDen E + 2 * (u * (tenDen E * twoDen eB)))
    (hw : 6 * (u * (tenDen E * twoDen eB)) ≤ w * (tenDen E * twoDen eB)) :
    leadM m E - 767 ≤ eB := by
  have hprox : valNum m E * twoDen eB ≤ 2 * (boundNum J eB * tenDen E) :=
    proximity_scale hV hB hw
  have hnear : valLeqBoundary m E (2 * J) eB := by
    rw [valLeqBoundary_iff_cross]
    have h2 : boundNum (2 * J) eB = 2 * boundNum J eB := by
      unfold boundNum
      rw [Nat.mul_assoc]
    rw [h2]
    simpa only [Nat.mul_assoc] using hprox
  exact shift_of_near hm hJ heB hlead hnear

/-! ### The arm at the supplied environment and staging

`JsonStage2NumFastArm.NumFastBodyArm` takes two parameters: a `Calls` selection
that answers the three out-of-line callees, and a staging that stages the two
tables (`NumFastTables`).  Both are values now rather than paragraphs —
`stage2NumFastCalls` answers the callees, with each site's `denoteCode` defined
and its step a jump (`JsonStage2NumFastCalls.numFast_ifEnd268_denote_some`,
`numFast_whileBodyPreheader_denote_some`, `numFast_ifThen178_denote_some`, with
their `_step_jump` forms), and `numFastTables_holds` is the staging at
`numFastTableEnv`/`numFastTableMem`.

**The kernel's bound is met at the body.**  `num_el_el1`'s mantissa is a
`uint64_t`, so `NumFastElAgrees` and `elGuardRefinesOn` are stated on
`w < 2 ^ 64`, and above it the guard's wrapped window test separates from the
model (`JsonStage2NumFastTier2.not_numFastElUnbounded`).  At the body's own
site the mantissa is `%add244`, a 64-bit word, so the bound holds without a side
condition: `numFast_ifEnd268_domain` is the site's run with `a.toNat < 2 ^ 64`
alongside it.  The bound is the kernel's, and the body stays inside it.

**What is still open is the conversion's run.**  At the supplied environment the
three `_ub` theorems of `JsonStage2NumFastArm` no longer describe the run — they
describe `s2HelperCalls`, and they are kept for exactly that.  What a proof must
still supply is the region's `runFuel` simulation, block by block: the three
digit runs' arms (`JsonStage2NumFastScan.numFastScanBoundLoop`'s `step_exit` and
`step_loop`), the eight-digit fast path's `cleanup` block, the register tie at
`if.end230` (`%ip.5708717729` and `%fr.5718728` against `Decimal.digitsNat`), and
tier 3's region.  Tier 3's three named links are now closed at their statements:
the traversal with the trip count (`t3_traversal_counts_1_3`), the window's copy
(`copy_retained`, `copy_sticky`, `copy_counters`, and the store's own step
`t3_copy_denote`), and the proximity estimate at the tree's rounding
(`roundMag_dist_le_step`, `proximity_scale`, `t3_scale_of_ulp`).  The region's
remaining blocks start with `for.body.i.i566.i.i.epil`, which the traversal hands
to, so the arm's tier-3 obligation is now a simulation over named blocks rather
than a missing step at the poison edge. -/

/-- **The kernel's domain at the body's own site.**  `if.end268`'s mantissa is
`%add244`, a 64-bit word, so `NumFastElAgrees`'s `w < 2 ^ 64` bound is the body's
own and not a condition the arm adds. -/
theorem numFast_ifEnd268_domain {epow : Int → Option EPow} {env : Env} {s : State}
    {a b : BitVec 64} {q : Nat}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    ∃ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x ∧
      denoteCode (stage2NumFastCalls epow) numFastIfEnd268Instrs (stateAt env s) =
        some (stateAt
          (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
           ("%call270", .int 32 x) :: env)
          { s with mem := r.mem, next := r.next }) ∧
      a.toNat < 2 ^ 64 := by
  obtain ⟨r, x, hx, hcode⟩ := numFast_ifEnd268_denote_some epow ha hb hd
  exact ⟨r, x, hx, hcode, a.isLt⟩

/-! ### The regression: one poison `phi`, two successors

A two-block function whose head carries a poison-forwarding `phi` and a `condbr`,
and whose two successor blocks differ in one respect: `reader` reads the `phi`
destination and `keeper` does not.  Stepping the head must bind the marker and
jump; stepping `reader` must be `ub`, because the marker is in the cell and
`evalOperand` refuses it; stepping `keeper` must jump.  One theorem asserts all
three, so a selection that failed on the poison literal (the head would be `.ub`)
or that bound the destination to a readable value (`reader` would jump) fails it.
-/

/-- The `BitVec` shape `evalBinopNat .add` leaves at width 64 with the immediate
`1`: the `Nat` modulus is the `BitVec` sum. -/
theorem ofNat_add_one (c : BitVec 64) :
    BitVec.ofNat 64 ((c.toNat + 1) % 18446744073709551616) = c + 1 := by
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_ofNat, BitVec.toNat_add]

/-- The fixture: `%p = phi i64 [ poison, %entry ]` in `head`, a `condbr` on
`%t` to the two successors, `reader`'s one instruction reading `%p`, and
`keeper`'s reading `%c` instead. -/
def poisonPhiBody : Function :=
  { name := "poison.phi.fixture", retTy := .void, params := [],
    blocks :=
      [ { name := "head",
          instrs := [Instr.phi "%p" (Ty.int 64) [("entry", Operand.imm Const.poison)]],
          term := Term.condbr (Operand.reg "%t") "reader" "keeper" },
        { name := "reader",
          instrs := [Instr.binop "%x" BinOp.add 64 (Operand.reg "%p")
            (Operand.imm (Const.int 64 0x0000000000000001#64))],
          term := Term.unreachable },
        { name := "keeper",
          instrs := [Instr.binop "%y" BinOp.add 64 (Operand.reg "%c")
            (Operand.imm (Const.int 64 0x0000000000000001#64))],
          term := Term.br "reader" } ] }

theorem poisonPhi_findBlock_reader :
    poisonPhiBody.findBlock "reader" =
      some ⟨"reader",
        [Instr.binop "%x" BinOp.add 64 (Operand.reg "%p")
          (Operand.imm (Const.int 64 0x0000000000000001#64))],
        Term.unreachable⟩ := by
  decide

theorem poisonPhi_findBlock_keeper :
    poisonPhiBody.findBlock "keeper" =
      some ⟨"keeper",
        [Instr.binop "%y" BinOp.add 64 (Operand.reg "%c")
          (Operand.imm (Const.int 64 0x0000000000000001#64))],
        Term.br "reader"⟩ := by
  decide

/-- The regression.  One head, two successors, one state: the head binds the
marker and jumps; the successor that reads the cell is `ub`; the successor that
does not is a jump. -/
theorem poisonPhi_two_successors (env : Env) (s : State) {c : BitVec 64} {t : BitVec 1}
    (ht : lookupName env "%t" = some (.int 1 t)) (hbit : t = (1 : BitVec 1))
    (hc : lookupName env "%c" = some (.int 64 c)) :
    -- the head's run binds the marker and jumps: the poison incoming is a
    -- selection, not a block failure
    step noCalls poisonPhiBody (stateAt env { s with pc := "head", pre := some "entry" })
        = .jump (stateAt (("%p", .poison) :: env)
            { s with pc := "reader", pre := some "head" })
    ∧
    -- the successor that reads the cell: the marker is a use, so `ub`
    step noCalls poisonPhiBody
        (stateAt (("%p", .poison) :: env) { s with pc := "reader", pre := some "head" })
        = .ub
    ∧
    -- the successor that reads no poison cell: a jump
    step noCalls poisonPhiBody
        (stateAt (("%p", .poison) :: env) { s with pc := "keeper", pre := some "head" })
        = .jump (stateAt (("%y", .int 64 (c + 1)) :: ("%p", .poison) :: env)
            { s with pc := "reader", pre := some "keeper" }) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [step, poisonPhiBody, Function.findBlock, findBlockList,
      denoteCode, denoteRun, phiSelect, phiIncoming, evalOperand, lookupName,
      State.bindAll, State.bind, stateAt, ht, hbit, execTerm]
  · simp [step, poisonPhi_findBlock_reader, denoteCode, denoteRun, evalOperand,
      evalInstr, State.bindAll, stateAt]
  · simp [step, poisonPhi_findBlock_keeper, denoteCode, denoteRun, evalOperand,
      lookupName, evalInstr, Const.toValue, Value.intToNat, evalBinopNat,
      evalBinop, BitVec.ofNat_toNat, ofNat_add_one, State.bindAll, State.bind, stateAt,
      hc, execTerm]

end NumFastTier3

/-! ### Axiom footprints -/

#print axioms NumFastTier3.phiSelect_poison
#print axioms NumFastTier3.evalOperand_poison_cell
#print axioms NumFastTier3.denoteRun_poison_head
#print axioms NumFastTier3.denoteCode_poison_head
#print axioms NumFastTier3.denoteCode_poison_head_ub
#print axioms NumFastTier3.t3_poison_edge_ub
#print axioms NumFastTier3.t3_poison_edge_step_one
#print axioms NumFastTier3.t3_poison_edge_step_zero
#print axioms NumFastTier3.t3_poison_edge_runFuel
#print axioms NumFastTier3.t3_poison_cells_unread
#print axioms NumFastTier3.t3_entry_denote
#print axioms NumFastTier3.t3_entry_step_residual
#print axioms NumFastTier3.t3_entry_step_unrolled
#print axioms NumFastTier3.t3_residual_test_zero
#print axioms NumFastTier3.ofNat_add_one
#print axioms NumFastTier3.poisonPhi_two_successors
#print axioms NumFastTier3.t3_xtraiter_ofNat
#print axioms NumFastTier3.t3_entryEnv_xtraiter
#print axioms NumFastTier3.t3_entry_residual_bit
#print axioms NumFastTier3.t3_traversal_counts_1_3
#print axioms NumFastTier3.t3_traversal_markers
#print axioms NumFastTier3.digVal_append
#print axioms NumFastTier3.digVal_lt
#print axioms NumFastTier3.digVal_lt_drop
#print axioms NumFastTier3.digits_lt_drop
#print axioms NumFastTier3.digVal_eq_zero
#print axioms NumFastTier3.ndig_digVal
#print axioms NumFastTier3.copy_retained
#print axioms NumFastTier3.copy_sticky
#print axioms NumFastTier3.copy_counters
#print axioms NumFastTier3.copy_retained_window
#print axioms NumFastTier3.copy_sticky_window
#print axioms NumFastTier3.copy_S_window
#print axioms NumFastTier3.copy_lead_window
#print axioms NumFastTier3.t3_findBlock_copy
#print axioms NumFastTier3.step_store8
#print axioms NumFastTier3.t3_copy_denote
#print axioms NumFastTier3.t3PowConst_eq
#print axioms NumFastTier3.step_mul_imm_w
#print axioms NumFastTier3.denoteCode_mul_imm_w
#print axioms NumFastTier3.step_add_reg_w
#print axioms NumFastTier3.denoteCode_add_reg_w
#print axioms NumFastTier3.step_lshr_imm_w
#print axioms NumFastTier3.denoteCode_lshr_imm_w
#print axioms NumFastTier3.t3_findBlock_epil
#print axioms NumFastTier3.t3_epil_denote
#print axioms NumFastTier3.t3_epil_step_lcssa
#print axioms NumFastTier3.t3_epil_step_self
#print axioms NumFastTier3.roundMag_isMag
#print axioms NumFastTier3.lo_mul
#print axioms NumFastTier3.hi_mul
#print axioms NumFastTier3.dist_lo_le
#print axioms NumFastTier3.dist_hi_le
#print axioms NumFastTier3.roundMag_dist_le_step
#print axioms NumFastTier3.fmulBits_dist_le_step
#print axioms NumFastTier3.fdivBits_dist_le_step
#print axioms NumFastTier3.proximity_scale
#print axioms NumFastTier3.tenDen_pos
#print axioms NumFastTier3.twoDen_pos
#print axioms NumFastTier3.lt_or_eq_iff_le
#print axioms NumFastTier3.valLeqBoundary_iff_cross
#print axioms NumFastTier3.t3_scale_of_ulp
#print axioms NumFastTier3.numFast_ifEnd268_domain

end LeanLLVM.Refinement
