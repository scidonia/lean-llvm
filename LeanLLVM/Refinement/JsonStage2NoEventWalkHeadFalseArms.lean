/-
The no-event walk's head refusals: `if.end51.peel`'s and `if.end23`'s false arms,
their two refusal rows, and the `.loopexit` staging at a non-zero depth.

`JsonStage2NoEventWalkTrailingDeep` names the `k + 1 = K.nep` subcase of both
trailing exits and does not produce it: the peeled dispatch's `if.end51.peel`
refuses a `[` whose next entry is past the stream at `if.then321`, and the brace
prologue's `if.end23` refuses a `{` the same way at `if.then68`.  The committed
`link_ifEnd51peel` and `link_ifEnd23` (`JsonStage2NoEventWalkLoop`) state the true
arms only, so no row reaches either refusal block.  This module adds:

* the two false-arm links — the same blocks and `icmp`s at the zero bit;
* the two refusal rows the terminal lane's `stage2NoEventZeroBlock_row`
  (`JsonStage2NoEventWalkTerminalA`) makes of them: `if.then321` and `if.then68`
  store the three zero words and `%n` at `%err`, and `cleanup580` returns zero —
  the shape the trailing lane's `stage2NoEventWalkAfterValueRefuseRowOfEntry`
  already builds, reached here from the head's own guard rather than from a pair
  route's endpoint;
* the `.loopexit` staging at a non-zero depth: the six registers the continuation
  dispatch's chains (`stage2NoEventRow_loopExitBrace`/`_loopExitString`/
  `_loopScalar`, `JsonStage2NoEventWalkClose`) carry through the leaves to the
  stubs, read at each stub — the cells `if.end`'s `phi` run binds and the class's
  entry head (`JsonStage2NoEventWalkEntryRooted`) consumes.

**The dispatch to the entry, at depth ≠ 0.**  A head's own four dispatch rows
(`stage2NoEventRow_brace`/`_bracket`/`_string`/`_value`) stage the head's `%3`
at `NodeBlock5` through the leaves to `if.then9`/`if.then35.peel`/
`string_value`/`scalar`.  A continuation entry is at `NodeBlock15`, dispatched on
`%7`; its three-block chains to the `.loopexit` stubs are committed, and what
those chains leave unstated is the stub's reading of the six carried cells, which
this module proves.  A `NodeBlock15` state is produced from the head's own peeled
push — `stage2NoEventRow_bracketPush` reaches `if.end327.peel`, and
`ifEnd327peel_produce` runs `if.end327.peel` → `if.end` → `NodeBlock15`, its
`phi` run binding exactly `%7`, `%8`, `%indvars.iv`, `%k.0`, `%terms.0`,
`%tokens.0`, `%inc` — at the price of the push's staging (the next entry's lane
and byte reads, the caller's).  At a **counted-loop** iteration the dispatch state is produced too: `if.end` is
entered from `if.end327` with its `phi` inputs `%47`/`%46`/`%indvars.iv`/`%inc`/
`%terms.0`/`%tokens.0`, the array loop's own counter cells, and the committed
`ifEndProduce_fromEnd327` (with `ifEnd327_produce` in front of it) concludes the
`NodeBlock15` state with all seven cells — through `ifEnd327_produce`, which no
other module uses yet.  What a non-head entry lacks is the **route into
`if.end327`'s entry** at that iteration: the only committed producer of an
`if.end327` entry (`stage2NoEventWalkBracketInnerTo327`) starts from a
`NodeBlock15` dispatch state, so it cannot bootstrap the state it would feed.  The class's entry head then reads the six
through its own guard: `if.then9`'s `%cmp10 = (trunc %indvars.iv) ugt 519` must
be zero, so the depth supply is `%indvars.iv.toNat % 2 ^ 32 ≤ 519` — the
`.loopexit` entry head's own premise (`stage2NoEventWalkBraceEntryHead`'s
`hguard`), a bound and not a block.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkClose
import LeanLLVM.Refinement.JsonStage2NoEventWalkTerminalA
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerZero
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The two false arms

Each block is one `icmp` on an entry cursor against `%nep`; the true arms are the
committed `link_ifEnd51peel`/`link_ifEnd23`.  At the false bit the block's own
`denoteCode` is the same run with the cell at `0`, and the branch names the
refusal entry. -/

/-- **`if.end51.peel` at a spent entry stream**: the false arm, to `if.then321`.
`%inc.peel = k + 1` is not below `%nep`, so the peeled dispatch never reads an
entry and the block hands off to the `[]` refusal.  The block, the `icmp` and the
env cell are the true arm's; only the bit and the branch differ. -/
theorem link_ifEnd51peel_false {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {inc : BitVec 64} {nep : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end51.peel")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hnult : BitVec.ult inc nep = false) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%cmp319.not.peel", .int 1 0) :: s.env) s "if.then321") := by
  have hbit : evalICmp .ult inc nep = (0 : BitVec 1) := by
    show BitVec.ofBool (BitVec.ult inc nep) = 0
    rw [hnult]
    rfl
  have hcode : denoteCode calls ifEnd51peelBlock.instrs (stateAt s.env s) =
      some (stateAt (("%cmp319.not.peel", .int 1 0) :: s.env) s) := by
    rw [ifEnd51peelBlock, denoteCode_icmp_ult_reg (calls := calls)
      (env := s.env) (s := s) (d := "%cmp319.not.peel") (a := "%inc.peel")
      (b := "%nep") (x := inc) (y := nep) hinc hnep (is := [])]
    simp only [hbit, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_false
    (env' := ("%cmp319.not.peel", .int 1 0) :: s.env)
    h (by rw [hpc]; exact ifEnd51peelBlock_find) hcode rfl
    (by rw [lookupName_cons_self])

/-- **`if.end23` at a spent entry stream**: the false arm, to `if.then68`.  The
depth is raised (`%inc24 = %sp + 1`) and `%inc.lcssa1129` is not below `%nep`, so
the `{}` prologue hands off to the brace refusal.  Only the bit and the branch
differ from `link_ifEnd23`. -/
theorem link_ifEnd23_false {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32} {inc : BitVec 64} {nep : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end23")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hnult : BitVec.ult inc nep = false) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%cmp66.not", .int 1 0) ::
          ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: s.env) s "if.then68") := by
  have hbit : evalICmp .ult inc nep = (0 : BitVec 1) := by
    show BitVec.ofBool (BitVec.ult inc nep) = 0
    rw [hnult]
    rfl
  have hcode : denoteCode calls ifEnd23Block.instrs (stateAt s.env s) =
      some (stateAt
        (("%cmp66.not", .int 1 0) ::
          ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: s.env) s) := by
    rw [ifEnd23Block]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := s.env) (s := s)
      (d := "%inc24") (a := "%sp.0.lcssa1092.wide") (w := 32) hsp]
    rw [denoteCode_icmp_ult_reg (calls := calls)
      (env := ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: s.env) (s := s)
      (d := "%cmp66.not") (a := "%inc.lcssa1129") (b := "%nep")
      (x := inc) (y := nep)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hinc)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hnep) (is := [])]
    simp only [hbit, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_false (env' :=
    ("%cmp66.not", .int 1 0) ::
      ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: s.env)
    h (by rw [hpc]; exact ifEnd23Block_find) hcode rfl
    (by rw [lookupName_cons_self])

/-! ### The refusal rows

The false arm leaves a state at the refusal block's entry; the block is one of the
terminal lane's zero-store entries at `%n`, so its own control step, `cleanup580`'s
return and the record's boundary are `stage2NoEventZeroBlock_row`'s.  The route to
the guard block is the caller's — the peeled dispatch's push for `[]`, the brace
prologue for `{}` — exactly as the trailing lane's refusal takes its pair route. -/

/-- **The `[]` head's refusal row**, from the peeled dispatch's guard.  `h` is the
head, `hj` the caller's route to `if.end51.peel`'s entry (`sE`) with the invariant
there (`hinvE`), and the guard's two cells plus the zero bit make `if.then321` the
target; the row is the terminal lane's zero-store row at `%n`, priced at the route,
the guard block's step and the refusal block's (`hcost`). -/
noncomputable def stage2NoEventWalkBracketHeadRefuseRow {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {sE : State} {j : Nat} {inc nep : BitVec 64}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hinvE : Stage2NoEventWalkInv K mem sE)
    (hpc : sE.pc = "if.end51.peel")
    (hinc : lookupName sE.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName sE.env "%nep" = some (.int 64 nep))
    (hnult : BitVec.ult inc nep = false)
    (hbase : Stage2NoEventWalkBaseLookups K sE)
    (hcost : j + 2 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)))
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  classical
  let s1 : State := stage2NoEventWalkNext
    (("%cmp319.not.peel", .int 1 0) :: sE.env) sE "if.then321"
  have l : Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem sE K s1 :=
    link_ifEnd51peel_false (calls := stage2NoEventCalls gap) hinvE hpc hinc hnep hnult
  have hpc1 : s1.pc = "if.then321" := rfl
  have hmem1 : s1.mem = sE.mem := by simp only [s1, stage2NoEventWalkNext]
  have hbase1 : Stage2NoEventWalkBaseLookups K s1 :=
    stage2NoEventCycleBase (K := K) hbase (cs := [("%cmp319.not.peel", .int 1 0)])
      (names := ["%cmp319.not.peel"]) rfl (by decide)
  have hpar1 : Stage2NoEventWalkParams K s1 :=
    stage2NoEventWalkBaseLookups_params hbase1
  have hloc1 : Stage2NoEventWalkLocals K s1 :=
    stage2NoEventWalkBaseLookups_locals hbase1 h.inv.xjNext0
  have hw1 : lookupName s1.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hbase1 "%n" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hle1 : (BitVec.ofNat 64 K.n).toNat ≤ K.n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  have hj1 : ∀ n, runFuel (stage2NoEventCalls gap) (j + 1 + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody s1 := by
    intro n
    rw [show j + 1 + n = j + (1 + n) from by omega, hj (1 + n),
      stage2NoEventWalkLink_runFuel l n]
  have hreport1 : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem s1.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmem1]; exact hreport
  have hrouteFrame1 : UnchangedOutside s.mem s1.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) := by
    rw [hmem1]; exact hrouteFrame
  exact stage2NoEventZeroBlock_row (gap := gap) (F := F) (k := k) (sE := s1)
    (blk := "if.then321") (b := stage2NoEventIfThen321Block) (w := "%n")
    (x := BitVec.ofNat 64 K.n) h hj1 hpc1
    stage2NoEventIfThen321Block_find stage2NoEventIfThen321Block_instrs
    (by decide) (by decide) hpar1 hloc1 hw1 hle1 (by omega)
    hreport1 htrace hrouteFrame1 hdata

/-- **The `{}` head's refusal row**, from the brace prologue's guard.  `hj` is the
caller's route to `if.end23`'s entry, with the invariant there (`hinvE`); the false
arm raises the depth and leaves `%cmp66.not` at zero, and the refusal is
`if.then68`'s zero-store block — the terminal lane's row again, at the same `%n`
word. -/
noncomputable def stage2NoEventWalkBraceHeadRefuseRow {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {sE : State} {j : Nat} {sp : BitVec 32} {inc nep : BitVec 64}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hinvE : Stage2NoEventWalkInv K mem sE)
    (hpc : sE.pc = "if.end23")
    (hsp : lookupName sE.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hinc : lookupName sE.env "%inc.lcssa1129" = some (.int 64 inc))
    (hnep : lookupName sE.env "%nep" = some (.int 64 nep))
    (hnult : BitVec.ult inc nep = false)
    (hbase : Stage2NoEventWalkBaseLookups K sE)
    (hcost : j + 2 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)))
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hdata : Stage2NoEventWalkReferenceRefuse K) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  classical
  let s1 : State := stage2NoEventWalkNext
    (("%cmp66.not", .int 1 0) ::
      ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: sE.env) sE "if.then68"
  have l : Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem sE K s1 :=
    link_ifEnd23_false (calls := stage2NoEventCalls gap) hinvE hpc hsp hinc hnep hnult
  have hpc1 : s1.pc = "if.then68" := rfl
  have hmem1 : s1.mem = sE.mem := by simp only [s1, stage2NoEventWalkNext]
  have hbase1 : Stage2NoEventWalkBaseLookups K s1 :=
    stage2NoEventCycleBase (K := K) hbase
      (cs := [("%cmp66.not", .int 1 0),
        ("%inc24", .int 32 (sp + BitVec.ofNat 32 1))])
      (names := ["%cmp66.not", "%inc24"]) rfl (by decide)
  have hpar1 : Stage2NoEventWalkParams K s1 :=
    stage2NoEventWalkBaseLookups_params hbase1
  have hloc1 : Stage2NoEventWalkLocals K s1 :=
    stage2NoEventWalkBaseLookups_locals hbase1 h.inv.xjNext0
  have hw1 : lookupName s1.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hbase1 "%n" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hle1 : (BitVec.ofNat 64 K.n).toNat ≤ K.n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  have hj1 : ∀ n, runFuel (stage2NoEventCalls gap) (j + 1 + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody s1 := by
    intro n
    rw [show j + 1 + n = j + (1 + n) from by omega, hj (1 + n),
      stage2NoEventWalkLink_runFuel l n]
  have hreport1 : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem s1.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) := by
    rw [hmem1]; exact hreport
  have hrouteFrame1 : UnchangedOutside s.mem s1.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) := by
    rw [hmem1]; exact hrouteFrame
  exact stage2NoEventZeroBlock_row (gap := gap) (F := F) (k := k) (sE := s1)
    (blk := "if.then68") (b := stage2NoEventIfThen68Block) (w := "%n")
    (x := BitVec.ofNat 64 K.n) h hj1 hpc1
    stage2NoEventIfThen68Block_find stage2NoEventIfThen68Block_instrs
    (by decide) (by decide) hpar1 hloc1 hw1 hle1 (by omega)
    hreport1 htrace hrouteFrame1 hdata

/-! ### The `.loopexit` staging at a non-zero depth

The continuation dispatch (`NodeBlock15`) hands a class's entry to a two- or
three-block chain ending at the class's `.loopexit` stub (`if.then9.loopexit`,
`string_value.loopexit`, `scalar.loopexit`).  The chains are committed; what the
stub's entry head needs and the chains do not state is the six registers the
`if.end` `phi` run bound and the stub carries.  These three theorems read them at
the stub. -/

/-- **The `{` exit's staging**: `NodeBlock15`'s byte is `{` (123), and the chain
to `if.then9.loopexit` carries `%8`, `%indvars.iv`, `%inc`, `%k.0`, `%terms.0`
and `%tokens.0` through its three pivot cells. -/
theorem stage2NoEventWalkLoopExitBraceStaging {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 123)))
    {v8 : BitVec 32} {iv inc k0 terms tok : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 v8))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hk0 : lookupName s.env "%k.0" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok)) :
    ∃ sE, Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "if.then9.loopexit" ∧
      lookupName sE.env "%8" = some (.int 32 v8) ∧
      lookupName sE.env "%indvars.iv" = some (.int 64 iv) ∧
      lookupName sE.env "%inc" = some (.int 64 inc) ∧
      lookupName sE.env "%k.0" = some (.int 64 k0) ∧
      lookupName sE.env "%terms.0" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0" = some (.int 64 tok) := by
  let sE : State := stage2NoEventWalkAt
    (("%SwitchLeaf12", .int 1 1) :: ("%Pivot14", .int 1 0) ::
      ("%Pivot16", .int 1 0) :: s.env) s "if.then9.loopexit" "LeafBlock11"
  have hpcE : sE.pc = "if.then9.loopexit" := rfl
  refine ⟨sE, ?_, hpcE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sE] using
      stage2NoEventRow_loopExitBrace (calls := calls) h hpc h7
  all_goals
    simp only [sE, stage2NoEventWalkAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · exact h8
  · exact hiv
  · exact hinc
  · exact hk0
  · exact htr
  · exact htok

/-- **The `"` exit's staging**: `NodeBlock15`'s byte is `"` (34), and the chain
to `string_value.loopexit` carries the same six through `%Pivot16` and
`%SwitchLeaf8`. -/
theorem stage2NoEventWalkLoopExitStringStaging {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 34)))
    {v8 : BitVec 32} {iv inc k0 terms tok : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 v8))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hk0 : lookupName s.env "%k.0" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok)) :
    ∃ sE, Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "string_value.loopexit" ∧
      lookupName sE.env "%8" = some (.int 32 v8) ∧
      lookupName sE.env "%indvars.iv" = some (.int 64 iv) ∧
      lookupName sE.env "%inc" = some (.int 64 inc) ∧
      lookupName sE.env "%k.0" = some (.int 64 k0) ∧
      lookupName sE.env "%terms.0" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0" = some (.int 64 tok) := by
  let sE : State := stage2NoEventWalkAt
    (("%SwitchLeaf8", .int 1 1) :: ("%Pivot16", .int 1 1) :: s.env)
    s "string_value.loopexit" "LeafBlock7"
  have hpcE : sE.pc = "string_value.loopexit" := rfl
  refine ⟨sE, ?_, hpcE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sE] using
      stage2NoEventRow_loopExitString (calls := calls) h hpc h7
  all_goals
    simp only [sE, stage2NoEventWalkAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · exact h8
  · exact hiv
  · exact hinc
  · exact hk0
  · exact htr
  · exact htok

/-- **The scalar exit's staging**: `NodeBlock15`'s byte is none of `34`, `91`,
`123`, and whichever leaf the pivot range selects, the chain to `scalar.loopexit`
carries the same six.  The leaf is the committed `stage2NoEventRow_loopScalar`'s
three-way case; only the pivot cells differ. -/
theorem stage2NoEventWalkLoopExitScalarStaging {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy34 : y ≠ BitVec.ofNat 8 34) (hy91 : y ≠ BitVec.ofNat 8 91)
    (hy123 : y ≠ BitVec.ofNat 8 123)
    {v8 : BitVec 32} {iv inc k0 terms tok : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 v8))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hk0 : lookupName s.env "%k.0" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok)) :
    ∃ sE, Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "scalar.loopexit" ∧
      lookupName sE.env "%8" = some (.int 32 v8) ∧
      lookupName sE.env "%indvars.iv" = some (.int 64 iv) ∧
      lookupName sE.env "%inc" = some (.int 64 inc) ∧
      lookupName sE.env "%k.0" = some (.int 64 k0) ∧
      lookupName sE.env "%terms.0" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0" = some (.int 64 tok) := by
  rcases stage2NoEventRow_loopScalar (calls := calls) h hpc h7 hy34 hy91 hy123 with
    ⟨hch, -⟩ | ⟨hch, -⟩ | ⟨hch, -⟩
  · refine ⟨_, hch, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [stage2NoEventWalkAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · exact h8
    · exact hiv
    · exact hinc
    · exact hk0
    · exact htr
    · exact htok
  · refine ⟨_, hch, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [stage2NoEventWalkAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · exact h8
    · exact hiv
    · exact hinc
    · exact hk0
    · exact htr
    · exact htok
  · refine ⟨_, hch, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [stage2NoEventWalkAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · exact h8
    · exact hiv
    · exact hinc
    · exact hk0
    · exact htr
    · exact htok

/-! ### Axiom footprints -/

#print axioms link_ifEnd51peel_false
#print axioms link_ifEnd23_false
#print axioms stage2NoEventWalkBracketHeadRefuseRow
#print axioms stage2NoEventWalkBraceHeadRefuseRow
#print axioms stage2NoEventWalkLoopExitBraceStaging
#print axioms stage2NoEventWalkLoopExitStringStaging
#print axioms stage2NoEventWalkLoopExitScalarStaging

end LeanLLVM.Refinement
