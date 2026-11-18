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
  `ub` above is the local obstruction.  The peeled nest's own entry is now
  stepped (`t3_entry_step_residual`/`t3_entry_step_unrolled`): its test is
  `%inc12 <u 4`, so the poison edge is taken exactly at a peeled count below
  four, and the caller excludes only zero.  A trip-count argument cannot
  therefore make the edge unreachable, and the residual question is the model's
  all-or-nothing refusal of an unread `poison` `phi` — see the section below.
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

What that fixes.  A trip-count argument that would make the poison edge
unreachable cannot be an argument about the peel itself: nothing at this block
excludes counts `1`, `2` or `3`, and the caller (`while.body173.i.i`) only
excludes zero.  On that path the block's `denoteCode` is `none` — the two
`poison` `phi`s resolve to nothing — so the model's `step` is `.ub` however the
successor then behaves, while the emitted code reads only the two well-defined
`phi`s (`%indvars…unr` and `%carry…unr` are a `0` immediate each) and takes the
epilogue branch whenever the residue is nonzero.  `t3_residual_test_zero` is
that reading: for a count inside `0 < k < 4` the residue is the count itself and
the epilogue test is refused, so the edge's poison is never read.  The residual
obligation is therefore not a trip-count bound the tree is missing; it is a
question about the model's all-or-nothing refusal of a `poison` `phi` — a
`poison` that the taken successor does not read — and that question is recorded
here rather than assumed away. -/

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

end NumFastTier3

/-! ### Axiom footprints -/

#print axioms NumFastTier3.phiSelect_poison
#print axioms NumFastTier3.denoteCode_poison_head
#print axioms NumFastTier3.t3_poison_edge_ub
#print axioms NumFastTier3.t3_poison_edge_runFuel_ub
#print axioms NumFastTier3.t3_entry_denote
#print axioms NumFastTier3.t3_entry_step_residual
#print axioms NumFastTier3.t3_entry_step_unrolled
#print axioms NumFastTier3.t3_residual_test_zero

end LeanLLVM.Refinement
