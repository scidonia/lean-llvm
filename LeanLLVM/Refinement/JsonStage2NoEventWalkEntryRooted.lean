/-
The no-event walk's descend classes, rooted at their entry.

`JsonStage2NoEventWalkDescendClasses` proves that no `Stage2NoEventWalkHead` holds
at a class's entry, so the head-rooted producers for `{`, `"` and the scalar
class cannot be applied where the continuation dispatch puts them.  This module
does two things for those three classes, and names what is left.

**The entry head.**  Each class's entry block is a two-instruction stub
(`if.then9.loopexit`, `string_value.loopexit`, `scalar.loopexit`) that computes the
entry index and the depth word, and the class's own head block then runs its
`phi`s at the stub's edge.  `JsonStage2NoEventWalkClose` has both blocks' links;
this module *composes* them and states the class's head cells at the entry's own
registers.  That is the re-rooting: the cells the class's route reads are proved
available from the entry state's environment, not from a `Stage2NoEventWalkHead`.

**The row without the head.**  Two of the committed row producers use the head for
exactly one field.  `stage2NoEventWalkStringRow_cont_of_route` and
`stage2NoEventWalkValueRow_cont_of_route` (with `Stage2NoEventWalkValueRoute.cycleSrc`)
read `h.count` and nothing else.  The versions below take that bound as the
caller's supply, so the row is stated at *any* state whose route and consumed
count are known — in particular at the class's entry.  The head disappears from
the statement rather than being faked at an entry where it is false.

**What is left, per class.**

* `"`: the four-block prefix from `if.end216`'s entry to `LeafBlock27`'s entry
  (`if.end216`, `if.end230`, the call in `if.end239`, `NodeBlock29`) is proved
  inside `JsonStage2NoEventWalkRowsString`'s `stage2NoEventWalkStringHeadToLeaf27`,
  which is a seven-block segment to `LeafBlock27` stated with a head; it is not
  exported at a generic `if.end216` state, and `LeafBlock27`'s own step to the
  arm's entry is not in it.  The entry segment below ends where that prefix
  begins.
* scalar: the value provider (`JsonStage2NoEventWalkValue`'s
  `stage2NoEventWalkValueLeaf`/`…Leaf1`/`…Leaf3`) runs from a `NodeBlock5` head
  through `cond.true`, `cond.end`, `land.lhs.true`/`if.end457` and the four arms;
  it is not exported from `scalar`'s post-`phi` branch.  The entry segment below
  reaches that branch (`cond.true` / `cond.end`).
* `{`: the prologue continues from `if.then9` through the push and the next
  entry's read to `NodeBlock21`'s entry; the four links exist
  (`link_ifEnd19`, `link_ifThen20`, `link_ifEnd23`, `link_ifEnd74`) and the key
  route from `NodeBlock21` is exported generically
  (`stage2NoEventWalkKeyRoute_of_leafBlock17` over
  `Stage2NoEventWalkEntryAPrologue`).  What is missing is the prologue's cell
  assembly at the loop exit's edge, not a block.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkDescendClasses
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsString
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsValue

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### `{`: the brace head at the brace exit's edge

`if.then9.loopexit` computes `%idxprom.le1289 = zext %8` and `%9 = trunc
%indvars.iv`, and `if.then9`'s seven `phi`s then select that edge's operands, with
`%frame.0.lcssa1098` the constant `1` (`ifThen9AtLoopexitCells`).  The two links
are `link_ifThen9LoopexitEntry` and `link_ifThen9AtLoopexit_false`; this composes
them and reads back the cells the prologue's remaining four blocks consume. -/

/-- **The `{` class's head at its entry**: two blocks from `if.then9.loopexit` to
`if.end19`, and the seven `phi` cells at the entry's own registers.  `%8` is the
entry's lane word and `%indvars.iv` the array stack's cursor, so the depth the
push reads is the loop's own, not a head's. -/
theorem stage2NoEventWalkBraceEntryHead {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then9.loopexit")
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    {inc k terms tok : BitVec 64}
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hguard : evalICmp .ugt (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))
      (BitVec.ofNat 32 519) = 0) :
    ∃ sE : State,
      Stage2NoEventWalkSegment calls mem K s K sE 2 ∧
      sE.pc = "if.end19" ∧
      lookupName sE.env "%sp.0.lcssa1092.wide" =
        some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ∧
      lookupName sE.env "%frame.0.lcssa1098" = some (.int 8 1) ∧
      lookupName sE.env "%k.0.lcssa1086" = some (.int 64 k) ∧
      lookupName sE.env "%terms.0.lcssa1080" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0.lcssa1074" = some (.int 64 tok) ∧
      lookupName sE.env "%idxprom.lcssa1108" =
        some (.int 64 (BitVec.ofNat 64 w.toNat)) ∧
      lookupName sE.env "%inc.lcssa1129" = some (.int 64 inc) ∧
      lookupName sE.env "%cmp10" = some (.int 1 0) := by
  let sp9 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let idx : BitVec 64 := BitVec.ofNat 64 w.toNat
  let S1 : State := stage2NoEventWalkNext
    (("%9", .int 32 sp9) :: ("%idxprom.le1289", .int 64 idx) :: s.env) s "if.then9"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifThen9LoopexitEntry h hpc h8 hiv
  have hpc1 : S1.pc = "if.then9" := by simp only [S1, stage2NoEventWalkNext]
  have hpre1 : S1.pre = some "if.then9.loopexit" := by
    simp only [S1, stage2NoEventWalkNext, hpc]
  have hinc1 : lookupName S1.env "%inc" = some (.int 64 inc) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hidx1 : lookupName S1.env "%idxprom.le1289" = some (.int 64 idx) := by
    simp only [S1, stage2NoEventWalkNext, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have h9_1 : lookupName S1.env "%9" = some (.int 32 sp9) := by
    simp only [S1, stage2NoEventWalkNext, sp9]
    simp only [lookupName_cons_self]
  have hk1 : lookupName S1.env "%k.0" = some (.int 64 k) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htr1 : lookupName S1.env "%terms.0" = some (.int 64 terms) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htok1 : lookupName S1.env "%tokens.0" = some (.int 64 tok) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hguard' : evalICmp .ugt sp9 (BitVec.ofNat 32 519) = 0 := hguard
  let L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext
        (ifThen9AtLoopexitCells S1.env inc idx sp9 k terms tok) S1 "if.end19") :=
    link_ifThen9AtLoopexit_false (calls := calls) L1.inv' hpc1 hpre1
      hinc1 hidx1 h9_1 hk1 htr1 htok1 hguard'
  let sE : State := stage2NoEventWalkNext
    (ifThen9AtLoopexitCells S1.env inc idx sp9 k terms tok) S1 "if.end19"
  have hspE : lookupName sE.env "%sp.0.lcssa1092.wide" = some (.int 32 sp9) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hfrE : lookupName sE.env "%frame.0.lcssa1098" = some (.int 8 1) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hkE : lookupName sE.env "%k.0.lcssa1086" = some (.int 64 k) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htrE : lookupName sE.env "%terms.0.lcssa1080" = some (.int 64 terms) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htokE : lookupName sE.env "%tokens.0.lcssa1074" = some (.int 64 tok) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hidxE : lookupName sE.env "%idxprom.lcssa1108" = some (.int 64 idx) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hincE : lookupName sE.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hcmpE : lookupName sE.env "%cmp10" = some (.int 1 0) := by
    simp only [sE, stage2NoEventWalkNext, ifThen9AtLoopexitCells, sp9, idx]
    rw [lookupName_cons_self, hguard]
  exact ⟨sE, (stage2NoEventWalkStringRowLinkSegment L1).trans
      (stage2NoEventWalkStringRowLinkSegment L2), rfl, hspE, hfrE, hkE, htrE, htokE,
    hidxE, hincE, hcmpE⟩

/-! ### `"`: the string head at the string exit's edge

`string_value.loopexit` computes `%idxprom.le1287` and `%28`, and `string_value`'s
eight `phi`s then select the edge's operands with `%frame.0.lcssa1099 = 1`; the
lifetime marker is the block's call and the end test is `%cmp207.not`.  The two
links are `link_stringValueLoopexitEntry` and `link_stringValue_true`. -/

/-- **The `"` class's head at its entry**: two blocks from `string_value.loopexit`
to `if.end216`, and the eight `phi` cells at the entry's own registers.  The
lifetime marker's outcome is the caller's supply because it is a call. -/
theorem stage2NoEventWalkStringEntryHead {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "string_value.loopexit")
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    {inc : BitVec 64} {k terms tok nep : BitVec 64}
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    {o : Nat}
    (houtn : lookupName s.env "%outn205" = some (.ptr o))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    {r : CallOutcome}
    (hcall : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r)
    (hmem : r.mem = s.mem) (hnext : r.next = s.next)
    (hguard : evalICmp .ult inc nep = 1) :
    ∃ sE : State,
      Stage2NoEventWalkSegment calls mem K s K sE 2 ∧
      sE.pc = "if.end216" ∧
      sE.mem = r.mem ∧ sE.next = s.next ∧
      lookupName sE.env "%inc.lcssa1130" = some (.int 64 inc) ∧
      lookupName sE.env "%.lcssa1125" = some (.int 32 w) ∧
      lookupName sE.env "%idxprom.lcssa1109" =
        some (.int 64 (BitVec.ofNat 64 w.toNat)) ∧
      lookupName sE.env "%frame.0.lcssa1099" = some (.int 8 1) ∧
      lookupName sE.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ∧
      lookupName sE.env "%k.0.lcssa1087" = some (.int 64 k) ∧
      lookupName sE.env "%terms.0.lcssa1081" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0.lcssa1075" = some (.int 64 tok) ∧
      lookupName sE.env "%cmp207.not" = some (.int 1 (evalICmp .ult inc nep)) := by
  let sp28 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let idx : BitVec 64 := BitVec.ofNat 64 w.toNat
  let S1 : State := stage2NoEventWalkNext
    (("%28", .int 32 sp28) :: ("%idxprom.le1287", .int 64 idx) :: s.env)
    s "string_value"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_stringValueLoopexitEntry h hpc h8 hiv
  have hpc1 : S1.pc = "string_value" := by simp only [S1, stage2NoEventWalkNext]
  have hpre1 : S1.pre = some "string_value.loopexit" := by
    simp only [S1, stage2NoEventWalkNext, hpc]
  have hinc1 : lookupName S1.env "%inc" = some (.int 64 inc) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have h8_1 : lookupName S1.env "%8" = some (.int 32 w) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h8
  have hidx1 : lookupName S1.env "%idxprom.le1287" = some (.int 64 idx) := by
    simp only [S1, stage2NoEventWalkNext, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hsp1 : lookupName S1.env "%28" = some (.int 32 sp28) := by
    simp only [S1, stage2NoEventWalkNext, sp28]
    simp only [lookupName_cons_self]
  have hk1 : lookupName S1.env "%k.0" = some (.int 64 k) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htr1 : lookupName S1.env "%terms.0" = some (.int 64 terms) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htok1 : lookupName S1.env "%tokens.0" = some (.int 64 tok) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htok
  have houtn1 : lookupName S1.env "%outn205" = some (.ptr o) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have hnep1 : lookupName S1.env "%nep" = some (.int 64 nep) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hcall' : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] S1.mem S1.next = some r := by
    simp only [S1, stage2NoEventWalkNext]
    exact hcall
  have hmem' : r.mem = S1.mem := by
    simp only [S1, stage2NoEventWalkNext]; exact hmem
  have hnext' : r.next = S1.next := by
    simp only [S1, stage2NoEventWalkNext]; exact hnext
  let L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext
        (stringValueCells S1.env inc w idx sp28 k terms tok nep) S1 "if.end216") :=
    link_stringValue_true (calls := calls) L1.inv' hpc1 hpre1 hinc1 h8_1 hidx1
      hsp1 hk1 htr1 htok1 houtn1 hnep1 hcall' hmem' hnext' hguard
  let sE : State := stage2NoEventWalkNext
    (stringValueCells S1.env inc w idx sp28 k terms tok nep) S1 "if.end216"
  have hmemE : sE.mem = r.mem := by
    simp only [sE, stage2NoEventWalkNext]; exact hmem.symm
  have hnextE : sE.next = s.next := by
    simp only [sE, S1, stage2NoEventWalkNext]
  have hincE : lookupName sE.env "%inc.lcssa1130" = some (.int 64 inc) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hlcE : lookupName sE.env "%.lcssa1125" = some (.int 32 w) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hidxE : lookupName sE.env "%idxprom.lcssa1109" = some (.int 64 idx) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hfrE : lookupName sE.env "%frame.0.lcssa1099" = some (.int 8 1) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hspE : lookupName sE.env "%sp.0.lcssa1093.wide" = some (.int 32 sp28) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hkE : lookupName sE.env "%k.0.lcssa1087" = some (.int 64 k) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htrE : lookupName sE.env "%terms.0.lcssa1081" = some (.int 64 terms) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htokE : lookupName sE.env "%tokens.0.lcssa1075" = some (.int 64 tok) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hcmpE : lookupName sE.env "%cmp207.not"
      = some (.int 1 (evalICmp .ult inc nep)) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    simp only [lookupName_cons_self]
  exact ⟨sE, (stage2NoEventWalkStringRowLinkSegment L1).trans
      (stage2NoEventWalkStringRowLinkSegment L2), rfl, hmemE, hnextE, hincE, hlcE,
    hidxE, hfrE, hspE, hkE, htrE, htokE, hcmpE⟩

/-! ### scalar: the value head at the value exit's edge

`scalar.loopexit` computes `%idxprom.le1291` and `%55`, and `scalar`'s seven `phi`s
then select the edge's operands with `%frame.0.lcssa1097 = 1`; the block forms the
byte's address and the end test `%cmp436`.  The two links are
`link_scalarLoopexitEntry` with `link_scalar_true`/`link_scalar_false`. -/

/-- **The scalar class's head at its entry, the end test taken**: two blocks from
`scalar.loopexit` to `cond.true`, at the entry's own index, lane word and depth. -/
theorem stage2NoEventWalkScalarEntryHead_true {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar.loopexit")
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    {inc : BitVec 64} {bv : BitVec 8} {terms tok nep : BitVec 64}
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hbv : lookupName s.env "%7" = some (.int 8 bv))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hguard : evalICmp .ult inc nep = 1) :
    ∃ sE : State,
      Stage2NoEventWalkSegment calls mem K s K sE 2 ∧
      sE.pc = "cond.true" ∧
      lookupName sE.env "%cmp436" = some (.int 1 (evalICmp .ult inc nep)) ∧
      lookupName sE.env "%arrayidx6.le1046" =
        some (.ptr (K.b + ((BitVec.ofNat 64 w.toNat).signExtend 64).toNat)) ∧
      lookupName sE.env "%inc.lcssa" = some (.int 64 inc) ∧
      lookupName sE.env "%idxprom.lcssa" =
        some (.int 64 (BitVec.ofNat 64 w.toNat)) ∧
      lookupName sE.env "%.lcssa" = some (.int 8 bv) ∧
      lookupName sE.env "%frame.0.lcssa1097" = some (.int 8 1) ∧
      lookupName sE.env "%sp.0.lcssa1091.wide" =
        some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ∧
      lookupName sE.env "%terms.0.lcssa1079" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0.lcssa1073" = some (.int 64 tok) := by
  let sp9 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let idx : BitVec 64 := BitVec.ofNat 64 w.toNat
  let S1 : State := stage2NoEventWalkNext
    (("%55", .int 32 sp9) :: ("%idxprom.le1291", .int 64 idx) :: s.env) s "scalar"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_scalarLoopexitEntry h hpc h8 hiv
  have hpc1 : S1.pc = "scalar" := by simp only [S1, stage2NoEventWalkNext]
  have hpre1 : S1.pre = some "scalar.loopexit" := by
    simp only [S1, stage2NoEventWalkNext, hpc]
  have hinc1 : lookupName S1.env "%inc" = some (.int 64 inc) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hidx1 : lookupName S1.env "%idxprom.le1291" = some (.int 64 idx) := by
    simp only [S1, stage2NoEventWalkNext, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hbv1 : lookupName S1.env "%7" = some (.int 8 bv) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hbv
  have hsp1 : lookupName S1.env "%55" = some (.int 32 sp9) := by
    simp only [S1, stage2NoEventWalkNext, sp9]
    simp only [lookupName_cons_self]
  have htr1 : lookupName S1.env "%terms.0" = some (.int 64 terms) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htok1 : lookupName S1.env "%tokens.0" = some (.int 64 tok) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hb1 : lookupName S1.env "%b" = some (.ptr K.b) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hnep1 : lookupName S1.env "%nep" = some (.int 64 nep) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hpos : (idx.signExtend 64).toNat < 2 ^ 63 := by
    have hlane : w.toNat < 2 ^ 32 := w.isLt
    simpa only [idx] using stage2NoEventLane_signExtend_lt hlane
  let L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext
        (scalarCells S1.env inc idx bv sp9 terms tok nep
          (K.b + (idx.signExtend 64).toNat)) S1 "cond.true") :=
    link_scalar_true (calls := calls) L1.inv' hpc1 hpre1 hinc1 hidx1 hbv1 hsp1
      htr1 htok1 hb1 hnep1 hpos hguard
  let sE : State := stage2NoEventWalkNext
    (scalarCells S1.env inc idx bv sp9 terms tok nep
      (K.b + (idx.signExtend 64).toNat)) S1 "cond.true"
  have hcmpE : lookupName sE.env "%cmp436"
      = some (.int 1 (evalICmp .ult inc nep)) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    simp only [lookupName_cons_self]
  have harrE : lookupName sE.env "%arrayidx6.le1046"
      = some (.ptr (K.b + (idx.signExtend 64).toNat)) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hincE : lookupName sE.env "%inc.lcssa" = some (.int 64 inc) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hidxE : lookupName sE.env "%idxprom.lcssa" = some (.int 64 idx) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hlcE : lookupName sE.env "%.lcssa" = some (.int 8 bv) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hfrE : lookupName sE.env "%frame.0.lcssa1097" = some (.int 8 1) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hspE : lookupName sE.env "%sp.0.lcssa1091.wide" = some (.int 32 sp9) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htrE : lookupName sE.env "%terms.0.lcssa1079" = some (.int 64 terms) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htokE : lookupName sE.env "%tokens.0.lcssa1073" = some (.int 64 tok) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  exact ⟨sE, (stage2NoEventWalkStringRowLinkSegment L1).trans
      (stage2NoEventWalkStringRowLinkSegment L2), rfl, hcmpE, harrE, hincE, hidxE,
    hlcE, hfrE, hspE, htrE, htokE⟩

/-- **The scalar class's head at its entry, the end test not taken**: two blocks
from `scalar.loopexit` to `cond.end`. -/
theorem stage2NoEventWalkScalarEntryHead_false {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar.loopexit")
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    {inc : BitVec 64} {bv : BitVec 8} {terms tok nep : BitVec 64}
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hbv : lookupName s.env "%7" = some (.int 8 bv))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hguard : evalICmp .ult inc nep = 0) :
    ∃ sE : State,
      Stage2NoEventWalkSegment calls mem K s K sE 2 ∧
      sE.pc = "cond.end" ∧
      lookupName sE.env "%cmp436" = some (.int 1 (evalICmp .ult inc nep)) ∧
      lookupName sE.env "%inc.lcssa" = some (.int 64 inc) ∧
      lookupName sE.env "%idxprom.lcssa" =
        some (.int 64 (BitVec.ofNat 64 w.toNat)) ∧
      lookupName sE.env "%.lcssa" = some (.int 8 bv) ∧
      lookupName sE.env "%frame.0.lcssa1097" = some (.int 8 1) ∧
      lookupName sE.env "%sp.0.lcssa1091.wide" =
        some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ∧
      lookupName sE.env "%terms.0.lcssa1079" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0.lcssa1073" = some (.int 64 tok) := by
  let sp9 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let idx : BitVec 64 := BitVec.ofNat 64 w.toNat
  let S1 : State := stage2NoEventWalkNext
    (("%55", .int 32 sp9) :: ("%idxprom.le1291", .int 64 idx) :: s.env) s "scalar"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_scalarLoopexitEntry h hpc h8 hiv
  have hpc1 : S1.pc = "scalar" := by simp only [S1, stage2NoEventWalkNext]
  have hpre1 : S1.pre = some "scalar.loopexit" := by
    simp only [S1, stage2NoEventWalkNext, hpc]
  have hinc1 : lookupName S1.env "%inc" = some (.int 64 inc) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hidx1 : lookupName S1.env "%idxprom.le1291" = some (.int 64 idx) := by
    simp only [S1, stage2NoEventWalkNext, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hbv1 : lookupName S1.env "%7" = some (.int 8 bv) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hbv
  have hsp1 : lookupName S1.env "%55" = some (.int 32 sp9) := by
    simp only [S1, stage2NoEventWalkNext, sp9]
    simp only [lookupName_cons_self]
  have htr1 : lookupName S1.env "%terms.0" = some (.int 64 terms) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htok1 : lookupName S1.env "%tokens.0" = some (.int 64 tok) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hb1 : lookupName S1.env "%b" = some (.ptr K.b) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hnep1 : lookupName S1.env "%nep" = some (.int 64 nep) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hpos : (idx.signExtend 64).toNat < 2 ^ 63 := by
    have hlane : w.toNat < 2 ^ 32 := w.isLt
    simpa only [idx] using stage2NoEventLane_signExtend_lt hlane
  let L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext
        (scalarCells S1.env inc idx bv sp9 terms tok nep
          (K.b + (idx.signExtend 64).toNat)) S1 "cond.end") :=
    link_scalar_false (calls := calls) L1.inv' hpc1 hpre1 hinc1 hidx1 hbv1 hsp1
      htr1 htok1 hb1 hnep1 hpos hguard
  let sE : State := stage2NoEventWalkNext
    (scalarCells S1.env inc idx bv sp9 terms tok nep
      (K.b + (idx.signExtend 64).toNat)) S1 "cond.end"
  have hcmpE : lookupName sE.env "%cmp436"
      = some (.int 1 (evalICmp .ult inc nep)) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    simp only [lookupName_cons_self]
  have hincE : lookupName sE.env "%inc.lcssa" = some (.int 64 inc) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hidxE : lookupName sE.env "%idxprom.lcssa" = some (.int 64 idx) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hlcE : lookupName sE.env "%.lcssa" = some (.int 8 bv) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hfrE : lookupName sE.env "%frame.0.lcssa1097" = some (.int 8 1) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hspE : lookupName sE.env "%sp.0.lcssa1091.wide" = some (.int 32 sp9) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htrE : lookupName sE.env "%terms.0.lcssa1079" = some (.int 64 terms) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htokE : lookupName sE.env "%tokens.0.lcssa1073" = some (.int 64 tok) := by
    simp only [sE, stage2NoEventWalkNext, scalarCells, sp9, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  exact ⟨sE, (stage2NoEventWalkStringRowLinkSegment L1).trans
      (stage2NoEventWalkStringRowLinkSegment L2), rfl, hcmpE, hincE, hidxE,
    hlcE, hfrE, hspE, htrE, htokE⟩

/-! ### The row without the head

The committed string row reads the head for `h.count` only; the committed value
row reads it for `h.count` only, through `Stage2NoEventWalkValueRoute.cycleSrc`.
Both are restated here with that bound as the caller's supply, so the row is
available at any state whose route and count are known — the class's entry
included. -/

/-- **The string class's continuing row, at any state**, from its route and the
consumed-count bound.  Identical to `stage2NoEventWalkStringRow_cont_of_route`
except that the head is gone; `count` is the only field it read. -/
noncomputable def stage2NoEventWalkStringRow_cont_of_route_count {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (count : Stage2NoEventWalkCount K k)
    (route : Stage2NoEventWalkStringRoute calls mem K k s)
    (hcredit : route.jHead + route.jTail +
      stage2NoEventWalkPotential route.Kc (k + 2) ≤
        stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  have hklt : k + 2 + 1 < route.Kc.nep := by
    have := route.klt
    omega
  have hkaddr : k + 2 + 1 < 2 ^ 63 := by
    have := route.kAddr
    omega
  have hcount : Stage2NoEventWalkCount route.Kc (k + 2) := by
    unfold Stage2NoEventWalkCount at count ⊢
    rw [route.tokEq]
    omega
  have hsrc : Stage2NoEventWalkCycleSrc calls mem route.Kc (k + 2) route.sA :=
    { inv := route.segTail.inv'
      pc := route.pc
      frame := route.frame
      frameLt := route.frameLt
      frameNe := route.frameNe
      sp := route.sp
      spLt := route.spLt
      spNe := route.spNe
      kAddr := hkaddr
      klt := hklt
      count := hcount
      phiRun := route.after
      baseLookups := route.base
      bPos := route.bPos
      trace := route.trace
      comma := route.comma }
  let cw := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' : State := Classical.choose cw
  let p : Nat := Classical.choose (Classical.choose_spec cw)
  have hcyc : Stage2NoEventWalkCycle calls mem route.Kc (k + 2) route.sA 1 s' p :=
    Classical.choose_spec (Classical.choose_spec cw)
  refine stage2NoEventWalkRow_cont_of_afterValue (F := F)
    (route.segHead.trans route.segTail) hsrc hcyc
    route.nepEq route.a12Eq route.next0Eq (by omega) ?_
  exact hcredit

/-- **The value route's after-value cycle source, from the consumed count**
instead of the head.  The committed `Stage2NoEventWalkValueRoute.cycleSrc` reads
`h.count` for the endpoint's bound and nothing else; this is the same bundle with
that bound taken as the supply. -/
noncomputable def Stage2NoEventWalkValueRoute.cycleSrc_count {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (count : Stage2NoEventWalkCount K k)
    (route : Stage2NoEventWalkValueRoute calls mem K k s) :
    Stage2NoEventWalkCycleSrc calls mem route.K' route.knext route.sA := by
  have hklt : route.knext + 1 < route.K'.nep := by
    simpa only [route.knextEq] using route.klt
  have hkaddr : route.knext + 1 < 2 ^ 63 := by
    have h1 : route.knext + 1 = k + 2 := by rw [route.knextEq]
    have h2 : k + 2 < route.K'.nep := route.klt
    have h3 : route.K'.nep ≤ route.K'.n := route.armSeg.inv'.nepLe
    have h4 : route.K'.n ≤ 2 ^ 32 := by
      simpa only [stage2MaxDocument] using route.armSeg.inv'.maxDoc
    have h5 : route.K'.nep ≤ 2 ^ 32 := le_trans h3 h4
    have h6 : route.K'.nep < 2 ^ 63 := by omega
    exact lt_of_lt_of_le hklt (le_of_lt h6)
  have hcount : Stage2NoEventWalkCount route.K' route.knext :=
    Stage2NoEventWalkCount.step (a := 1) (b := 1) count route.tokEq
      route.knextEq (by omega)
  have hphi : ∃ p, route.sA.pre = some p ∧
      PhiSelects (stateAt route.sA.env route.sA) p afterValuePhiSpecs
        [("%frame.6", .int 8 (BitVec.ofNat 8 route.fr)),
         ("%sp.4", .int 32 (BitVec.ofNat 32 route.sp)),
         ("%k.6", .int 64 (BitVec.ofNat 64 route.knext)),
         ("%alen.8", .int 64 (BitVec.ofNat 64 route.K'.arena.length)),
         ("%arena.10", .int 64 (BitVec.ofNat 64 route.K'.arenaWord)),
         ("%terms.8", .int 64 (BitVec.ofNat 64 route.K'.terms)),
         ("%tokens.8", .int 64 (BitVec.ofNat 64 route.K'.tok))] := by
    rcases route.after.pre with hp | hp
    · exact ⟨"while.body557", hp,
        valueArmsAfter_phiSelects route.after "while.body557" hp (Or.inl rfl)⟩
    · exact ⟨"if.end545", hp,
        valueArmsAfter_phiSelects route.after "if.end545" hp (Or.inr rfl)⟩
  exact
    { inv := route.armSeg.inv'
      pc := route.after.pc
      frame := route.fr
      frameLt := route.frameLt
      frameNe := route.frameNe
      sp := route.sp
      spLt := route.spLt
      spNe := route.spNe
      kAddr := hkaddr
      klt := hklt
      count := hcount
      phiRun := hphi
      baseLookups := route.base
      bPos := route.bPos
      trace := route.trace
      comma := route.comma }

/-- **The value class's continuing row, at any state**, from its route and the
consumed-count bound.  Identical to `stage2NoEventWalkValueRow_cont_of_route`
except that the head is gone. -/
noncomputable def stage2NoEventWalkValueRow_cont_of_route_count {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (count : Stage2NoEventWalkCount K k)
    (route : Stage2NoEventWalkValueRoute calls mem K k s)
    (hcredit : route.jprov + route.jarm +
      stage2NoEventWalkPotential route.K' route.knext ≤
        stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  have hsrc := route.cycleSrc_count count
  have hknext : route.knext = k + 1 := route.knextEq
  let cw := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' : State := Classical.choose cw
  have hcwspec := Classical.choose_spec cw
  let p := Classical.choose hcwspec
  have hcyc : Stage2NoEventWalkCycle calls mem route.K' route.knext route.sA 1 s' p :=
    Classical.choose_spec hcwspec
  refine stage2NoEventWalkRow_cont_of_afterValue (F := F) route.seg hsrc hcyc
    route.nepEq route.a12Eq route.next0Eq (by omega) ?_
  exact hcredit

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBraceEntryHead
#print axioms stage2NoEventWalkStringEntryHead
#print axioms stage2NoEventWalkScalarEntryHead_true
#print axioms stage2NoEventWalkScalarEntryHead_false
#print axioms stage2NoEventWalkStringRow_cont_of_route_count
#print axioms Stage2NoEventWalkValueRoute.cycleSrc_count
#print axioms stage2NoEventWalkValueRow_cont_of_route_count

end LeanLLVM.Refinement
