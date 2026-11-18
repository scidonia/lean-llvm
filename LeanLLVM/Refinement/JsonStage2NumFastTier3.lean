/-
Tier 3 at the body: what the poison edges are, and where the traversal stops.

`JsonStage2NumFastArm` names the fallback's region — the inlined `num_scan`
second reader and the inlined `to_double` — and three links between the model
(`StrtodTier3.tier3Mag`) and the body's blocks: a `runFuel` simulation of the
region, the tie of the window's retained digits `M`, its scale `S` and the
sticky bit to `Decimal.mantissa`/`exponent`/`stkDrop`, and the proximity
estimate the tier-3 module still records.  This module states the first
obstruction of the first link and records the boundary of the other two.

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

**What that is not.**  A defined edge is not a worked-out traversal.  The
`runFuel` simulation must still reach this block on the lexemes the fallback
reaches, which is a trip-count fact about the peeled nests
(`for.body.lr.ph.i.i564.i.i` is the zero-trip entry of the `1088`-iteration
loop nest, and the region's own guard decides whether it is entered).  The tree
has no step lemma for any other block of the region, so the simulation that would
carry that argument does not exist; this module records the block's own step and
names the entry trip count as the first thing the simulation must decide.

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

The three links `JsonStage2NumFastArm` lists for this region, and what the tree
supplies for each:

* **The run.**  The region runs from `if.end285` (`num_scan`'s inline second
  reader) through `to_double` to `if.end291`'s store.  No block of it has a step
  lemma.  The peeled nest's own entry is stepped
  (`t3_entry_step_residual`/`t3_entry_step_unrolled`): its test is
  `%inc12 <u 4`, so the residual edge is taken exactly at a peeled count below
  four, and the caller excludes only zero — a trip-count argument cannot make
  that edge unreachable.  The residual block's own step is now supplied
  (`t3_poison_edge_step_one`/`t3_poison_edge_step_zero`): the two poisoned
  `phi`s bind the marker, neither is read, and the block jumps.  What is still
  open is the rest of the region's simulation, block by block.
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
proves the first block-level facts the first one needs. -/

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

end LeanLLVM.Refinement
