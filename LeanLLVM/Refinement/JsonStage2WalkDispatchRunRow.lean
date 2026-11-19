/-
# The run class's leaf, one producer per leaf, and the row at each

`HcontRunLeaf` (`JsonStage2WalkDispatchSeams`) is the byte's own leaf below
`if.else387.i`: its endpoint, the endpoint's invariant, the tail's three call rows at it,
the root slot's word, the carry's two bounds and the `phi`'s own edge with the kind
literal it selects.  The six builders are `hcontRunLeaf_letters` … `_58Else`
(`JsonStage2WalkDispatchClassCase`), and each takes the seam's three call rows *at its own
leaf*.

What no module yet said is where those rows come from.  The seam's supply is
`HcontSeamAbi` (`JsonStage2WalkDispatchSeams`), and the kind literal the leaf's `phi`
selects is part of that supply: the literal is stored into the token record, the
value-position call's argument list is read at the post-store memory, and the leaf's
`hval` reads the `phi`'s selection — so a seam whose literal is not the leaf's cannot
serve it.  `HcontSeamAbi`'s four continuing fields therefore carry their literal
(`HcontSeamKind`), and this module is the wiring: one producer per leaf, taking the field
that leaf's edge needs.

## Which supply item each leaf takes

| leaf | the seam's state | kind | supply item |
|---|---|---|---|
| the letters route (`LetS413`) | `contWsTailStart …` | `0` | `HcontClassRows.seamScan` (empty) |
| `'f'` (`FS413`) | `FS413 (contWsSeamS …)` | `9` | `HcontSeamAbi.scanF` |
| `110` (`ClsS413T`) | `ClsS413T (contWsSeamS …)` | `10` | `HcontSeamAbi.scan56True` |
| `111 … 115` (`ClsS413F`) | `contWsTailStart …` | `0` | `HcontClassRows.seamScan` (empty) |
| `116` (`ClsS58T`) | `ClsS58T (contWsSeamS …)` | `8` | `HcontSeamAbi.scan58True` |
| `117 … 125` (`HeadS413`) | `contWsTailStart …` | `0` | `HcontClassRows.seamScan` (empty) |

**The three emit items are the supply, and the three kind-`0` cells have none.**  `scanF`,
`scan56True` and `scan58True` are new rows: their leaves' predecessors are
`if.then397.i`, `if.then403.i` and `LeafBlock58`, whose `phi` incomings are `9`, `10` and
`8`, and no cast of another leaf's rows could discharge the leaf's `hval`
(`HcontRunLeaf.cA_of_imm` states exactly that the leaf pins its seam's literal).  The three
kind-`0` leaves read `HcontClassRows.seamScan`, the emit group at `if.else405.i`'s literal
`0`, and **that group is empty**: `od_scalar_value` answers `0` at a zero kind, so the walk
leaves for `if.then432.i` and never reaches `if.then447.i`
(`JsonStage2WalkDispatchSeamCalls.hcontSeamCalls_no_literal_zero`).  The three wrappers are
therefore the cells the coverage must stop claiming at those bytes; the field is stated
rather than assumed so that the stop is visible, and the rows that edge really carries are
`HcontSeamAbi.scanRefuse`'s (`JsonStage2WalkDispatchClassCase`'s
`hcontSeamRefuseAt_letters`/`_56Else`/`_58Else`).

## The row: a producer now, not a field

`HcontRunRow` used to be a payload field (`HcontClassRows.runRow`) whose argument was the
leaf.  It is now **produced**: `hcontRunRow_of_rows` derives the head part — the class's
prefix to `sw.default.i`, the shared four's cells, the entry's lane and the byte before the
entry's end — from the prefix segment's invariant and the payload's row, and takes the
document part as the arguments the reshape names: the run's body (`hcontRunBody_of_skip`,
from `runSkip`'s class), the record the scalar call appends, and `HcontRunRows`
(`runTail`).  There is one `HcontRunRow` and one producer; the old field is gone.

The leaf stays the producer's argument and is built per leaf by the six
`hcontRunLeafAt_*`: the case pairs the two, which is what makes the cell
`.run` × `wsByte` at every default class reachable from the payload's groups.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassCase
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassTransport

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### A leaf's literal is its seam's

The `phi` selects the literal from the predecessor's edge, and the leaf's `hval` reads that
selection.  So a leaf whose operand is the literal pins its seam's `cA`, which is why the
three nonzero-kind leaves cannot be cast from the `0` seam's rows. -/

/-- **A leaf whose `phi` selects a literal pins its seam's kind literal.**  `hval` is
`evalOperand (stateAt ss.env ss) op = some (.int 32 calls.cA)`; with `op` the literal, the
left side is that literal and the right the seam's word.  This is the theorem a producer
needs to see that a cast from another literal cannot serve: the cast preserves `cA`, so the
two rows are two memories, not one row at two states. -/
theorem HcontRunLeaf.cA_of_imm {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (leaf : HcontRunLeaf G C) {w : Nat}
    (h : leaf.op = Operand.imm (.int 32 (BitVec.ofNat 32 w))) :
    leaf.calls.cA = BitVec.ofNat 32 w := by
  have hval := leaf.hval
  rw [h] at hval
  simp only [evalOperand, Const.toValue, Option.some.injEq, Value.int.injEq, heq_eq_eq,
    true_and] at hval
  exact hval.symm

/-! ### The letters route's leaf: the class row's empty `seamScan` item -/

/-- **The letters route's leaf, from the class row's `seamScan`.**  `lettersSpan` ends at
`LetS413`, whose predecessor is `if.else405.i`; the item it reads is that edge's emit group,
which is empty, so this cell is vacuous.  It stays because
`JsonStage2WalkDispatchContinuing`'s `hcontArm_run_defaultValueLow` call site still reaches
it; the refusal rows for the same leaf are `hcontSeamRefuseAt_letters`'s. -/
noncomputable def hcontRunLeafAt_letters {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hc : HcontClassRows G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seamScan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_letters G C sl b35 ix v k x1 hInvS h8 (hc.seamScan C sl b35 ix v k x1).calls
    (hc.seamScan C sl b35 ix v k x1).hcA hroot0 hk h110 hne102

/-! ### The `'f'` leaf: the `scanF` item, whose literal is `9` -/

/-- **The `'f'` leaf, from its own seam rows.**  `fSpan` ends at `FS413`, whose `phi`
incoming is `if.then397.i`'s `9`; the rows are `scanF`'s and no cast from the `0` seam
could stand in for them (`HcontRunLeaf.cA_of_imm`). -/
noncomputable def hcontRunLeafAt_fLetter {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hs : HcontSeamAbi G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hs.scanF C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 1) :
    HcontRunLeaf G C :=
  hcontRunLeaf_fLetter G C sl b35 ix v k x1 hInvS h8 (hs.scanF C sl b35 ix v k x1).calls
    (hs.scanF C sl b35 ix v k x1).hcA hroot0 hk h110 h102

/-! ### `110`'s leaf: the `scan56True` item, whose literal is `10` -/

/-- **`110`'s leaf, from its own seam rows.**  `c56TrueSpan` ends at `ClsS413T`, whose
`phi` incoming is `if.then403.i`'s `10`. -/
noncomputable def hcontRunLeafAt_56True {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hs : HcontSeamAbi G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hs.scan56True C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 1) :
    HcontRunLeaf G C :=
  hcontRunLeaf_56True G C sl b35 ix v k x1 hInvS h8
    (hs.scan56True C sl b35 ix v k x1).calls
    (hs.scan56True C sl b35 ix v k x1).hcA hroot0 hk h110 h116 h110eq

/-! ### `111 … 115`'s leaf: the class row's empty `seamScan` item, cast -/

/-- **`111 … 115`'s leaf, from the class row's `seamScan`.**  `c56ElseSpan` ends at
`ClsS413F`, whose predecessor is `if.else405.i`; the item is that edge's emit group, which
is empty, so this cell is vacuous (the refusal rows are `hcontSeamRefuseAt_56Else`'s). -/
noncomputable def hcontRunLeafAt_56Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hc : HcontClassRows G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seamScan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_56Else G C sl b35 ix v k x1 hInvS h8 (hc.seamScan C sl b35 ix v k x1).calls
    (hc.seamScan C sl b35 ix v k x1).hcA hroot0 hk h110 h116 h110eq

/-! ### `116`'s leaf: the `scan58True` item, whose literal is `8` -/

/-- **`116`'s leaf, from its own seam rows.**  `c58TrueSpan` ends at `ClsS58T`, whose
`phi` incoming is `LeafBlock58`'s own `8`. -/
noncomputable def hcontRunLeafAt_58True {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hs : HcontSeamAbi G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hs.scan58True C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 1) :
    HcontRunLeaf G C :=
  hcontRunLeaf_58True G C sl b35 ix v k x1 hInvS h8
    (hs.scan58True C sl b35 ix v k x1).calls
    (hs.scan58True C sl b35 ix v k x1).hcA hroot0 hk h110 h116 h116eq

/-! ### `117 … 125`'s leaf: the class row's empty `seamScan` item, cast -/

/-- **`117 … 125`'s leaf, from the class row's `seamScan`.**  `c58ElseSpan` ends at
`HeadS413`, whose predecessor is `if.else405.i`; the item is that edge's emit group, which
is empty, so this cell is vacuous (the refusal rows are `hcontSeamRefuseAt_58Else`'s). -/
noncomputable def hcontRunLeafAt_58Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hc : HcontClassRows G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seamScan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_58Else G C sl b35 ix v k x1 hInvS h8 (hc.seamScan C sl b35 ix v k x1).calls
    (hc.seamScan C sl b35 ix v k x1).hcA hroot0 hk h110 h116 h116eq

/-! ### The run's row, from the class's prefix and the payload's two groups

`HcontRunRow`'s head part — the class's prefix to `sw.default.i`, the shared four's cells
and the check state's byte — is derived here; its document part is the payload's
(`runSkip`'s class, `runTail`'s rows).  The reshape this module carries is that the row is
**no longer a supply item**: `HcontClassRows.runRow`'s old field is gone, and
`hcontRunRow_of_rows` is its producer, taking the body, the record and the rows the
instruction names.

**Why the prefix data is an argument and the document rows are not.**  The class's chain to
`sw.default.i` ends at a state whose *name* differs per head class (`lowS₃`, `midS₄`,
`othS₄`, `brkS₄`, `bhS₄`, `brcS₄`), and the case composes it (`contLowToDefault` …
`contBrcToDefault`); the row's cells are then the invariant's at that endpoint, which is
what makes this producer class-independent.  The document rows, by contrast, are rows: the
payload carries them and the case passes them through.

**The memory tie.**  The default arm's prefix binds registers only, so `q5.mem = s.mem` is
the fact that makes the lane's read and the byte's read the head state's.  It is an
argument rather than a field because it is a theorem at every default class (`rfl`). -/

/-- `%8` at the check state is `sw.default.i`'s: none of the suffix's four blocks rebinds
it. -/
theorem contRunCheck_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contRunCheck G C q5 inc nep ep v ix b35).env "%8" =
      lookupName q5.env "%8" := by
  simp only [contRunCheck, contLandOut, contMidS, condEnd349OutAt, cte345OutAt, contSwOut,
    stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%idxprom.i` at the check state is `contSwOut`'s: neither the bound's store nor the
byte's pivots rebind it. -/
theorem contRunCheck_idx {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contRunCheck G C q5 inc nep ep v ix b35).env "%idxprom.i" =
      lookupName (contSwOut q5 inc nep).env "%idxprom.i" := by
  simp only [contRunCheck, contLandOut, contMidS, condEnd349OutAt, cte345OutAt, contSwOut,
    stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The row's cells, split from its document rows

The row needs the class's prefix endpoint's cells; the body needs the check state's.  Both
are the same invariant's, so they are produced once (`hcontRunHeadCells_of_prefix`,
`hcontRunCheckCells_of_head`) and consumed by `hcontRunRow_of_rows`,
`hcontRunBody_of_skip` and the arm helper. -/

/-- **The class's prefix endpoint's cells**, at `sw.default.i`: the count cells, the index,
the token's two pointers, the shared four's lane read and the byte before the entry's end.
Nothing here is a document fact — all of it is `hPrefix.inv'`'s, peeled through the suffix's
one bind — except the lane's read and the byte's, which are the payload's row at the
endpoint's memory. -/
structure HcontRunHeadCells {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r : HcontDefaultRow G C s) (q5 : State) : Type where
  hInv : WalkInv G (HeadAC₄ C) q5
  hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 (hlastIncV C))
  hnep : evalOperand q5 (.reg "%nep") = some (.int 64 (hlastNepV G))
  hnext : evalICmp .ult (hlastIncV C) (hlastNepV G) = 1
  h5 : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%5" = some (.ptr G.ep)
  hi63 : (hlastIncV C).toNat < 2 ^ 63
  hread : readBytes (contSwOut q5 (hlastIncV C) (hlastNepV G)).mem
    (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes r.v.toNat 4)
  hidx : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%idxprom.i" =
    some (.int 64 (contIx G C))
  htok : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%t352.i" =
    some (.ptr C.stage.tok)
  hgap : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%gap.i" =
    some (.ptr (C.stage.tok + 20))
  hread35 : readBytes (contMidS C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
    (contIx G C)).mem ((G.b - 1) + r.v.toNat) 1 = some [contB35 G r.v]

/-- **The check state's cells**, at the leaf the skip stops at: the check's invariant, its
three cells and the seam's `%8`.  All five are the chain's: the invariant is
`contSwToLandSeg`'s at the head cells, and the cells are the suffix's peels. -/
structure HcontRunCheckCells {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r : HcontDefaultRow G C s) (q5 : State) : Type where
  hInvC : WalkInv G (ContAC₄ C) (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
    (contIx G C) (contB35 G r.v))
  h35 : evalOperand (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
    (contIx G C) (contB35 G r.v)) (.reg "%35") = some (.int 8 (cont35 (contB35 G r.v)))
  hidx : lookupName (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
    (contIx G C) (contB35 G r.v)).env "%idxprom.i" = some (.int 64 (contIx G C))
  hcond : lookupName (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
    (contIx G C) (contB35 G r.v)).env "%cond350.i" =
    some (.int 64 (BitVec.ofNat 64 r.v.toNat))

/-- **The head cells, from the prefix segment.**  Every cell is `hPrefix.inv'`'s, peeled
through `contSwOut`'s single bind; the lane's read is the payload's row at the endpoint's
memory (`hmem`), and the byte before the entry's end is the document's at the suffix's own
memory (`contMidS_docByte`). -/
noncomputable def hcontRunHeadCells_of_prefix {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (q5 : State) (nq : Nat)
    (hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 nq)
    (hmem : q5.mem = s.mem) : HcontRunHeadCells G C s r q5 := by
  have hInv5 : WalkInv G (HeadAC₄ C) q5 := hPrefix.inv'
  have hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 (hlastIncV C)) :=
    LeanLLVM.evalOperand_reg_of hInv5.inc_reg
  have hnep : evalOperand q5 (.reg "%nep") = some (.int 64 (hlastNepV G)) :=
    LeanLLVM.evalOperand_reg_of (hInv5.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
      (by simp [walkStaticRegs]))
  have hnext : evalICmp .ult (hlastIncV C) (hlastNepV G) = 1 := cont_ult_one G C hk
  have h5 : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact hInv5.ptrs.2.1
  have hi63 : (hlastIncV C).toNat < 2 ^ 63 := cont_hi63 G C hk
  have hread : readBytes (contSwOut q5 (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes r.v.toNat 4) := by
    have hsm : (contSwOut q5 (hlastIncV C) (hlastNepV G)).mem = s.mem := by
      simp only [contSwOut, State.bind, hmem]
    rw [hsm, cont_inc_toNat G C hk]
    exact r.hread
  have hidx : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind, contIx]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hInv5.idx_reg
  have htok : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%t352.i" =
      some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact hInv5.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgap : lookupName (contSwOut q5 (hlastIncV C) (hlastNepV G)).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hInv5.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hread35 : readBytes (contMidS C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C)).mem ((G.b - 1) + r.v.toNat) 1 = some [contB35 G r.v] := by
    have hq : r.v.toNat - 1 < G.n := by
      have hvle := r.hvle
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s q5 hInv hmem (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    have hv1 := r.hv1
    rw [show (G.b - 1) + r.v.toNat = G.b + (r.v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact
    { hInv := hInv5
      hinc := hinc
      hnep := hnep
      hnext := hnext
      h5 := h5
      hi63 := hi63
      hread := hread
      hidx := hidx
      htok := htok
      hgap := hgap
      hread35 := hread35 }

/-- **The check state's cells, from the head's and the prefix's invariant.**  The invariant
is `contSwToLandSeg`'s at the head cells, and `%35`/`%idxprom.i`/`%cond350.i` are the
suffix's own peels.  No `%8` here: the seam's byte is the check state's, which the arm
helper reads at `q5` (`contRunCheck_env8`). -/
noncomputable def hcontRunCheckCells_of_head {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} {r : HcontDefaultRow G C s} {q5 : State}
    (d : HcontRunHeadCells G C s r q5) : HcontRunCheckCells G C s r q5 := by
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5 (ContAC₄ C)
      (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v)) 4 :=
    contSwToLandSeg G C q5 d.hInv rfl d.hinc d.hnep d.hnext d.h5 d.hi63 d.hread d.hidx
      d.htok d.hgap r.hugt d.hread35
  exact
    { hInvC := hseg.inv'
      h35 := by
        refine LeanLLVM.evalOperand_reg_of ?_
        exact contLandOut_35 (contMidS C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
          (contIx G C)) r.v.toNat (contB35 G r.v)
      hidx := by
        rw [contRunCheck_idx]
        exact d.hidx
      hcond := by
        rw [contLandOut_cond, contMidS_cond] }

/-- The run's body, from the skip's class and the check state's cells.  The class
conjunct is `runSkip`'s own: the per-index run, the stop and the stop's place; the byte
before the entry's end being whitespace is the caller's guard, unfolded into the class's
first disjunct; the stop's place inside the entry is `cont_heicd_of`'s arithmetic, *not* a
field.  The check state's cells (`%8`, `%35`, `%idxprom.i`, `%cond350.i`, the compare)
enter as arguments, because they are the class's chain's — the six default prefixes reach
them at six differently-named states — while everything about the document is
`runSkip`'s. -/
noncomputable def hcontRunBody_of_skip {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hk : C.k + 1 < G.nep) (r : HcontDefaultRow G C s)
    (hws : wsStop G (r.v.toNat - 1)) (skip : HcontRunSkip G C s r)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (q5 : State)
    (hInvC : WalkInv G (ContAC₄ C) (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep
      r.v (contIx G C) (contB35 G r.v)))
    (h8c : evalOperand (contWsSeamS C
        (wsSlAt G (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
          (contB35 G r.v)) (contB35 G r.v) (contIx G C) r.v skip.k) skip.k
        (hlastByte G C)) (.reg "%8") = some (.int 8 (hlastByte G C)))
    (h35 : evalOperand (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
        (contIx G C) (contB35 G r.v)) (.reg "%35") = some (.int 8 (cont35 (contB35 G r.v))))
    (hidx : lookupName (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
        (contIx G C) (contB35 G r.v)).env "%idxprom.i" = some (.int 64 (contIx G C)))
    (hcond : lookupName (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
        (contIx G C) (contB35 G r.v)).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 r.v.toNat)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 r.v.toNat) (contIx G C) = 1) :
    HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v)) := by
  -- the byte before the entry's end is whitespace: the guard, unfolded
  have hcls : (evalICmp .slt (cont35 (contB35 G r.v)) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (cont35 (contB35 G r.v) + BitVec.ofNat 8 247)
        (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 (contB35 G r.v)) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 (contB35 G r.v)) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 (contB35 G r.v)) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 (contB35 G r.v)) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 (contB35 G r.v)) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 (contB35 G r.v)) (BitVec.ofNat 8 32) = 1) := by
    have hx : wsX G (r.v.toNat - 1) = cont35 (contB35 G r.v) := rfl
    have h := hws
    unfold wsStop at h
    rw [hx] at h
    exact h
  -- the stop is inside the entry
  have hentry : (contIx G C).toNat = entryPos G C.k := by
    rw [contIx, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (entryPos_lt_64 G C.k)
  have hik' : entryPos G C.k < skip.k := by rw [← hentry]; exact skip.hik
  have heicd : skip.k < r.v.toNat := by
    refine cont_heicd_of G C hk hws ?_ hik' hugt
    intro q hq hqk
    exact skip.hrun q (by omega) hqk
  exact
    { hInv := hInvC
      b35 := contB35 G r.v
      h35 := h35
      ix := contIx G C
      hidx := hidx
      v := r.v
      hcond := hcond
      hugt := hugt
      k := skip.k
      x1 := hlastByte G C
      hClass := ⟨hcls, skip.hrun, skip.hstop, skip.hik, skip.hinner, by omega⟩
      heicd := heicd
      h8c := h8c
      hbit := hbit
      hspan := r.hvle }

/-- **The run's row, from the class's prefix and the payload's groups.**  The head part is
derived: the count cells from `hPrefix.inv'`, the entry's lane from the payload's row at
the prefix's own memory, the shared four's cells through their one bind, and the byte before
the entry's end from the document.  The body, the record and the rows are the arguments the
instruction names; the body is the caller's `hcontRunBody_of_skip`, which is why the
payload's skip class and its rows are the only document supply. -/
noncomputable def hcontRunRow_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    (hk : C.k + 1 < G.nep) (r : HcontDefaultRow G C s)
    (q5 : State) (nq : Nat)
    (hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 nq)
    (hnq : nq ≤ 4) (hmem : q5.mem = s.mem)
    (b : HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v)))
    (leaf : HcontRunLeaf G C) (ev : EventRecord)
    (rows : HcontRunRows G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
        (contIx G C) (contB35 G r.v)) leaf.ss b.b35 b.ix b.v b.k b.x1
      leaf.calls.r₁ leaf.calls.r₂ leaf.calls.r₃ ev leaf.calls.cA leaf.calls.rdv leaf.calls.xA) :
    HcontRunRow G C s := by
  let d := hcontRunHeadCells_of_prefix hInv hk r q5 nq hPrefix hmem
  exact
    { q5 := q5
      nq := nq
      hPrefix := hPrefix
      hnq := hnq
      inc := hlastIncV C
      nep := hlastNepV G
      hinc := d.hinc
      hnep := d.hnep
      hnext := d.hnext
      ep := G.ep
      h5 := d.h5
      hi63 := d.hi63
      v := r.v
      hread := d.hread
      ix := contIx G C
      hidx := d.hidx
      htok := d.htok
      hgap := d.hgap
      hugt := r.hugt
      b35 := contB35 G r.v
      hread35 := d.hread35
      b := b
      leaf := leaf
      ev := ev
      rows := rows }

/-! ### The run class's arm at one leaf

The two-dimensional split's `.run` cells are assembled here: the class's prefix segment (the
six default classes reach `sw.default.i` at six differently-named states), the payload's
`runSkip` and `runTail`, and the *leaf's* span.  The span is chosen by the byte, not by the
prefix's class — `.defaultValueBracketHigh`'s `93 … 122` alone takes four leaves — so this
helper takes the leaf and its span, and the class branches below dispatch on the byte's
pivots.

`h8q` is the prefix endpoint's `%8`: the segment binds registers only, and `WalkInv` does
not name `%8`, so the endpoint's byte is the class's own peel (`lowS₃`'s, `midS₄`'s …). -/

/-- **The seam's `%8`, from the prefix endpoint's.**  The seam's byte is the check state's
(`wsSlAt_env8`, `seamS_env8`) and the check state's is `sw.default.i`'s
(`contRunCheck_env8`); `h8q` is the class's own peel. -/
theorem hcontRunSeamByte {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {r : HcontDefaultRow G C s} {q5 : State} (k : Nat)
    (h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C))) :
    evalOperand (contWsSeamS C
      (wsSlAt G (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v)) (contB35 G r.v) (contIx G C) r.v k) k (hlastByte G C))
      (.reg "%8") = some (.int 8 (hlastByte G C)) := by
  refine LeanLLVM.evalOperand_reg_of ?_
  simp only [contWsSeamS]
  rw [seamS_env8, wsSlAt_env8, contRunCheck_env8]
  exact h8q

/-- **The run's body with its defining equations.**  The equations are what a branch needs
because a `def`'s projections are opaque: the body's fields give the tag bit and the seam's
`%8`, but a leaf's pivots must be read off `x1`, and a span must be stated at the body's own
fields.  `hb35`/`hx1`/`hk` turn that opacity into rewrites. -/
structure HcontRunBodyAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r : HcontDefaultRow G C s) (q5 : State) (skip : HcontRunSkip G C s r) : Type where
  /-- The body at the class's check state. -/
  b : HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
    (contIx G C) (contB35 G r.v))
  hb35 : b.b35 = contB35 G r.v
  hx1 : b.x1 = hlastByte G C
  hk : b.k = skip.k

/-- **The run's body at the class's prefix endpoint, with its equations.**  The check
state's cells are the prefix's (`hcontRunHeadCells_of_prefix`, `hcontRunCheckCells_of_head`)
and the body is `hcontRunBody_of_skip`'s; `runSkip`'s class supplies `k` and the run. -/
noncomputable def hcontRunBodyAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep) (r : HcontDefaultRow G C s)
    (hws : wsStop G (r.v.toNat - 1))
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (skip : HcontRunSkip G C s r) (q5 : State) (nq : Nat)
    (hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 nq)
    (hmem : q5.mem = s.mem)
    (h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C))) :
    HcontRunBodyAt G C s r q5 skip := by
  let d := hcontRunHeadCells_of_prefix hInv hk r q5 nq hPrefix hmem
  let c := hcontRunCheckCells_of_head d
  let b := hcontRunBody_of_skip hk r hws skip hbit q5 c.hInvC
    (hcontRunSeamByte (r := r) (q5 := q5) skip.k h8q) c.h35 c.hidx c.hcond r.hugt
  exact { b := b, hb35 := rfl, hx1 := rfl, hk := rfl }

/-- **The run class's arm, at one leaf**, from the body, the leaf and the leaf's span.  The
check state's invariant is the prefix segment's (`hPrefix.inv'`), so this needs no cells:
`runTail` states the rows at it, `hcontRunRow_of_rows` builds the row, and `HcontClassRows.run`
joins the row to the arm at the span.  The span starts at the row's seam, which is the run's
endpoint at the skip's stop — the term the row's `seamS` unfolds to. -/
theorem hcontRunArmAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (skip : HcontRunSkip G C s r)
    (q5 : State) (nq : Nat)
    (hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 nq)
    (hnq : nq ≤ 4) (hmem : q5.mem = s.mem)
    (b : HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v)))
    (leaf : HcontRunLeaf G C) {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunSeamS G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
        (contB35 G r.v) b.b35 b.ix b.v b.k b.x1)
      (ContTailStartC C) leaf.ss nS)
    (hnS : nS ≤ 5) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨ev, rows⟩ := hc.runTail C s hInv hblock hk r hws q5 hPrefix.inv' hmem leaf b
  let row := hcontRunRow_of_rows hInv hk r q5 nq hPrefix hnq hmem b leaf ev rows
  have hSpan' : Seg (stage2Calls stage2SubCalls) G (ContSeamC C) row.seamS
      (ContTailStartC C) row.tailS nS := hSpan
  exact hc.run C s hInv hblock hk row hSpan' hnS

/-! ### The six default classes' `.run` cells

One theorem per head class, each with the leaf's span.  `defaultValueLow`, `_Mid`,
`otherValue` and `_Bracket` take one leaf each (the letters route); `_BracketHigh` takes four
and dispatches on the byte's pivots; `_Brace` takes the class-C else leaf.  Every theorem is
stated at the class's own terms and reads the body's equations (`hb35`, `hx1`, `hk`) where
the leaf's pivots and the span need them. -/

/-- **`.defaultValueLow`'s `.run` continuation.**  The byte's signed reading is below `44`, so
the leaf is the letters one (`slt %8 110` and `%8 ≠ 102` follow) and the span is
`lettersSpan`'s. **Vacuous cell.**  `%8 < 44` (and `%8 ≠ 34`) is on the `if.else405.i` edge: `od_scalar_value` answers `0` there, so the walk leaves for `if.then432.i` and this `.run` bundle — whose leaf's `calls` are the emit group — has no inhabitant (`JsonStage2WalkDispatchSeamCalls.hcontSeamCalls_no_literal_zero`).  The rows the leaf really carries are `HcontSeamAbi.scanRefuse`'s, wired by `hcontSeamRefuseAt_letters`.  The cell is proved only through `HcontClassRows.seamScan` and is the count to drop with it. -/
theorem hcontArm_run_defaultValueLow {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx44 : x.toInt < 44 := by simpa using toInt_lt_of_slt_one h44
  have hbitx := tag_zero_of_toInt_lt_44 (x := x) hx44
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
    rw [← hx]; exact hbitx
  have h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1 := by
    rw [← hx]
    exact slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0 := by
    rw [← hx]
    exact eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  -- the class's prefix to `sw.default.i`, its memory and its byte
  let q5 : State := lowS₃ s x
  have hq5 : q5 = lowS₃ s x := rfl
  have hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 3 := by
    rw [hq5]
    exact Seg.measure (contLowToDefault G C s hInv hblock h8 h91 h44 hne34)
  have hmem : q5.mem = s.mem := rfl
  have h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C)) := by
    have h : lookupName q5.env "%8" = some (.int 8 x) := by
      show lookupName (lowS₃ s x).env "%8" = some (.int 8 x)
      simp only [lowS₃, lowS₂, lowS₁, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      walk_read using h8
    rw [h, hx]
  let skip := hc.runSkip C s hInv hblock hk r hws
  let ba := hcontRunBodyAt hInv hk r hws hbit skip q5 3 hPrefix hmem h8q
  -- the seam's invariant, the leaf and the leaf's span
  let cl := contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
    (contB35 G r.v)
  obtain ⟨N, _, hrun, _⟩ :=
    contWsRunBody G C cl ba.b hk
  have hInvS : WalkInv G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) := hrun.inv'
  have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 1 := by
    rw [ba.hx1]; exact h110
  have hne102b : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 102) = 0 := by
    rw [ba.hx1]; exact hne102
  let leaf := hcontRunLeafAt_letters hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
    hInvS ba.b.h8c
    (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot hk h110b hne102b
  have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
      (ContTailStartC C) leaf.ss 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl ba.b.h8c
      h110b hne102b
  exact hcontRunArmAt hc hInv hblock hk r hws skip q5 3 hPrefix (by decide) hmem ba.b leaf
    hSpan (by decide)

/-! The remaining default classes' `.run` cells, one theorem each -/

/-- **`.defaultValueMid`'s `.run` continuation** — `58 < %8 < 91`, so the letters leaf. **Vacuous cell.**  `59 ≤ %8 < 91` is on the `if.else405.i` edge (no value byte), so the leaf's emit group has no inhabitant (`hcontSeamCalls_no_literal_zero`); the refusal rows for the same leaf are `hcontSeamRefuseAt_letters`'s. -/
theorem hcontArm_run_defaultValueMid {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx91 : x.toInt < 91 := by simpa using toInt_lt_of_slt_one h91
  have hge58 : 58 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h58
  have hbitx := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
    rw [← hx]; exact hbitx
  have h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1 := by
    rw [← hx]
    exact slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0 := by
    rw [← hx]
    exact eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let q5 : State := midS₄ s x
  have hq5 : q5 = midS₄ s x := rfl
  have hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 4 := by
    rw [hq5]
    exact Seg.measure (contMidToDefault G C s hInv hblock h8 h91 h44 h58 hne58)
  have hmem : q5.mem = s.mem := rfl
  have h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C)) := by
    have h : lookupName q5.env "%8" = some (.int 8 x) := by
      show lookupName (midS₄ s x).env "%8" = some (.int 8 x)
      simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      walk_read using h8
    rw [h, hx]
  let skip := hc.runSkip C s hInv hblock hk r hws
  let ba := hcontRunBodyAt hInv hk r hws hbit skip q5 4 hPrefix hmem h8q
  let cl := contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
    (contB35 G r.v)
  obtain ⟨N, _, hrun, _⟩ := contWsRunBody G C cl ba.b hk
  have hInvS : WalkInv G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) := hrun.inv'
  have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 1 := by
    rw [ba.hx1]; exact h110
  have hne102b : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 102) = 0 := by
    rw [ba.hx1]; exact hne102
  let leaf := hcontRunLeafAt_letters hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
    hInvS ba.b.h8c
    (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot hk h110b hne102b
  have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
      (ContTailStartC C) leaf.ss 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl ba.b.h8c
      h110b hne102b
  exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b leaf
    hSpan (by decide)

/-- **`.otherValue`'s `.run` continuation** — `44 ≤ %8 < 58` and the tag test clear, so the
letters leaf.  The tag bit is the constructor's own field. **Vacuous cell.**  This class's bytes are `46` and `47` (`46`/`47` with the tag bit clear), on the `if.else405.i` edge, so the leaf's emit group has no inhabitant (`hcontSeamCalls_no_literal_zero`); the refusal rows for the same leaf are `hcontSeamRefuseAt_letters`'s. -/
theorem hcontArm_run_otherValue {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbitx : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx58 : x.toInt < 58 := by simpa using toInt_lt_of_slt_one h58
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
    rw [← hx]; exact hbitx
  have h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1 := by
    rw [← hx]
    exact slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0 := by
    rw [← hx]
    exact eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let q5 : State := othS₄ s x
  have hq5 : q5 = othS₄ s x := rfl
  have hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 4 := by
    rw [hq5]
    exact Seg.measure (contOthToDefault G C s hInv hblock h8 h91 h44 h58 hne44)
  have hmem : q5.mem = s.mem := rfl
  have h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C)) := by
    have h : lookupName q5.env "%8" = some (.int 8 x) := by
      show lookupName (othS₄ s x).env "%8" = some (.int 8 x)
      simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      walk_read using h8
    rw [h, hx]
  let skip := hc.runSkip C s hInv hblock hk r hws
  let ba := hcontRunBodyAt hInv hk r hws hbit skip q5 4 hPrefix hmem h8q
  let cl := contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
    (contB35 G r.v)
  obtain ⟨N, _, hrun, _⟩ := contWsRunBody G C cl ba.b hk
  have hInvS : WalkInv G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) := hrun.inv'
  have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 1 := by
    rw [ba.hx1]; exact h110
  have hne102b : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 102) = 0 := by
    rw [ba.hx1]; exact hne102
  let leaf := hcontRunLeafAt_letters hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
    hInvS ba.b.h8c
    (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot hk h110b hne102b
  have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
      (ContTailStartC C) leaf.ss 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl ba.b.h8c
      h110b hne102b
  exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b leaf
    hSpan (by decide)

/-- **`.defaultValueBracket`'s `.run` continuation** — the byte `92`, so the letters leaf. **Vacuous cell.**  The class's byte is `92` (`\`), on the `if.else405.i` edge, so the leaf's emit group has no inhabitant (`hcontSeamCalls_no_literal_zero`); the refusal rows for the same leaf are `hcontSeamRefuseAt_letters`'s. -/
theorem hcontArm_run_defaultValueBracket {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hge91 : 91 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h91
  have hx93 : x.toInt < 93 := by simpa using toInt_lt_of_slt_one h93
  have hbitx := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
    rw [← hx]; exact hbitx
  have h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1 := by
    rw [← hx]
    exact slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0 := by
    rw [← hx]
    exact eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let q5 : State := brkS₄ s x
  have hq5 : q5 = brkS₄ s x := rfl
  have hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 4 := by
    rw [hq5]
    exact Seg.measure (contBrkToDefault G C s hInv hblock h8 h91 h123 h93 hne91)
  have hmem : q5.mem = s.mem := rfl
  have h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C)) := by
    have h : lookupName q5.env "%8" = some (.int 8 x) := by
      show lookupName (brkS₄ s x).env "%8" = some (.int 8 x)
      simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      walk_read using h8
    rw [h, hx]
  let skip := hc.runSkip C s hInv hblock hk r hws
  let ba := hcontRunBodyAt hInv hk r hws hbit skip q5 4 hPrefix hmem h8q
  let cl := contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
    (contB35 G r.v)
  obtain ⟨N, _, hrun, _⟩ := contWsRunBody G C cl ba.b hk
  have hInvS : WalkInv G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) := hrun.inv'
  have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 1 := by
    rw [ba.hx1]; exact h110
  have hne102b : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 102) = 0 := by
    rw [ba.hx1]; exact hne102
  let leaf := hcontRunLeafAt_letters hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
    hInvS ba.b.h8c
    (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot hk h110b hne102b
  have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
      (ContTailStartC C) leaf.ss 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl ba.b.h8c
      h110b hne102b
  exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b leaf
    hSpan (by decide)

/-- **`.defaultValueBrace`'s `.run` continuation** — the byte `124`, so the class-C span's
last leaf (`117 … 125`'s else arm). **Vacuous cell.**  The class's byte is `124` (`|`), on the `if.else405.i` edge, so the leaf's emit group has no inhabitant (`hcontSeamCalls_no_literal_zero`); the refusal rows for the same leaf are `hcontSeamRefuseAt_58Else`'s. -/
theorem hcontArm_run_defaultValueBrace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hge123 : 123 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h123
  have hx125 : x.toInt < 125 := by simpa using toInt_lt_of_slt_one h125
  have hbitx := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
    rw [← hx]; exact hbitx
  have h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0 := by
    rw [← hx]
    exact slt_zero_of_toInt_ge (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have h116 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 0 := by
    rw [← hx]
    exact slt_zero_of_toInt_ge (x := x) (a := BitVec.ofNat 8 116)
      (by simp only [toInt_8_116]; omega)
  have h116eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0 := by
    rw [← hx]
    exact eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 116)
      (by simp only [toInt_8_116]; omega)
  let q5 : State := brcS₄ s x
  have hq5 : q5 = brcS₄ s x := rfl
  have hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 4 := by
    rw [hq5]
    exact Seg.measure (contBrcToDefault G C s hInv hblock h8 h91 h123 h125 hne123)
  have hmem : q5.mem = s.mem := rfl
  have h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C)) := by
    have h : lookupName q5.env "%8" = some (.int 8 x) := by
      show lookupName (brcS₄ s x).env "%8" = some (.int 8 x)
      simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      walk_read using h8
    rw [h, hx]
  let skip := hc.runSkip C s hInv hblock hk r hws
  let ba := hcontRunBodyAt hInv hk r hws hbit skip q5 4 hPrefix hmem h8q
  let cl := contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
    (contB35 G r.v)
  obtain ⟨N, _, hrun, _⟩ := contWsRunBody G C cl ba.b hk
  have hInvS : WalkInv G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) := hrun.inv'
  have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 0 := by
    rw [ba.hx1]; exact h110
  have h116b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 116) = 0 := by
    rw [ba.hx1]; exact h116
  have h116eqb : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 116) = 0 := by
    rw [ba.hx1]; exact h116eq
  let leaf := hcontRunLeafAt_58Else hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
    hInvS ba.b.h8c
    (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot hk h110b h116b h116eqb
  have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
      (ContTailStartC C) leaf.ss 5 :=
    c58ElseSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl ba.b.h8c
      h110b h116b h116eqb
  exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b leaf
    hSpan (by decide)

/-- **`.defaultValueBracketHigh`'s `.run` continuation** — `93 … 122`, the one default class
whose byte spans the four routes below `if.else387.i`: `'f'` at `102`, the letters span
below `110` and not `102`, and the class-C span from `110` on, split by the same pivots the
emitted pair performs. **Mixed, and its kind-0 part is vacuous.**  `94 … 122` includes the three literals (`102`, `110`, `116`), whose emit rows are real (`scanF`/`scan56True`/`scan58True`), and every other byte of the range, which is on the `if.else405.i` edge: that sub-branch reads the empty `HcontClassRows.seamScan` and has no inhabitant (`hcontSeamCalls_no_literal_zero`).  Separating the two needs `WalkContinueFacts` restricted to the byte disjunction, which this case cannot supply; the refusal rows for the letters sub-branch are `hcontSeamRefuseAt_letters`'s. -/
theorem hcontArm_run_defaultValueBracketHigh {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hge93 : 93 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h93
  have hx123 : x.toInt < 123 := by simpa using toInt_lt_of_slt_one h123
  have hbitx := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
    rw [← hx]; exact hbitx
  have h125x : evalICmp .slt x (BitVec.ofNat 8 125) = 1 :=
    slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 125)
      (by simp only [toInt_8_125]; omega)
  have h125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1 := by
    rw [← hx]; exact Or.inl h125x
  let q5 : State := bhS₄ s x
  have hq5 : q5 = bhS₄ s x := rfl
  have hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 4 := by
    rw [hq5]
    exact Seg.measure (contBhToDefault G C s hInv hblock h8 h91 h123 h93 hne93)
  have hmem : q5.mem = s.mem := rfl
  have h8q : lookupName q5.env "%8" = some (.int 8 (hlastByte G C)) := by
    have h : lookupName q5.env "%8" = some (.int 8 x) := by
      show lookupName (bhS₄ s x).env "%8" = some (.int 8 x)
      simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      walk_read using h8
    rw [h, hx]
  let skip := hc.runSkip C s hInv hblock hk r hws
  let ba := hcontRunBodyAt hInv hk r hws hbit skip q5 4 hPrefix hmem h8q
  let cl := contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v (contIx G C)
    (contB35 G r.v)
  obtain ⟨N, _, hrun, _⟩ := contWsRunBody G C cl ba.b hk
  have hInvS : WalkInv G (ContSeamC C)
      (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) := hrun.inv'
  have root0 : readBytes (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).mem
      (G.next0 + 8) 4 =
      some (natToBytes (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).calls.rdv.toNat 4) :=
    (hc.seamScan C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot
  have rootF : readBytes (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).mem
      (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scanF C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).calls.rdv.toNat 4) :=
    (hc.seam.scanF C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot
  have root56T : readBytes (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).mem
      (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan56True C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).calls.rdv.toNat 4) :=
    (hc.seam.scan56True C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot
  have root58T : readBytes (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).mem
      (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan58True C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).calls.rdv.toNat 4) :=
    (hc.seam.scan58True C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1).hroot
  by_cases h110one : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1
  · have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 1 := by
      rw [ba.hx1]; exact h110one
    by_cases h102one : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 1
    · have h102b : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 102) = 1 := by
        rw [ba.hx1]; exact h102one
      let leaf := hcontRunLeafAt_fLetter hc.seam cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
        hInvS ba.b.h8c rootF hk h110b h102b
      have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
          (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
          (ContTailStartC C) leaf.ss 4 :=
        fSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
          (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl
          ba.b.h8c h110b h102b
      exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b
        leaf hSpan (by decide)
    · have h102z : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0 :=
        bitZeroOfNeOne h102one
      have hne102b : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 102) = 0 := by
        rw [ba.hx1]; exact h102z
      let leaf := hcontRunLeafAt_letters hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
        hInvS ba.b.h8c root0 hk h110b hne102b
      have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
          (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
          (ContTailStartC C) leaf.ss 4 :=
        lettersSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
          (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl
          ba.b.h8c h110b hne102b
      exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b
        leaf hSpan (by decide)
  · have h110z : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0 :=
      bitZeroOfNeOne h110one
    have h110b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 110) = 0 := by
      rw [ba.hx1]; exact h110z
    by_cases h110eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 110) = 1
    · have h110eqb : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 110) = 1 := by
        rw [ba.hx1]; exact h110eq
      have h116one : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 1 := by
        have hb110 : hlastByte G C = BitVec.ofNat 8 110 := (evalICmp_eq_one_iff _ _).1 h110eq
        rw [hb110]
        decide
      have h116b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 116) = 1 := by
        rw [ba.hx1]; exact h116one
      let leaf := hcontRunLeafAt_56True hc.seam cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1
        hInvS ba.b.h8c root56T hk h110b h116b h110eqb
      have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
          (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
          (ContTailStartC C) leaf.ss 5 :=
        c56TrueSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
          (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl
          ba.b.h8c h110b h116b h110eqb
      exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b
        leaf hSpan (by decide)
    · have h110eqz : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 110) = 0 :=
        bitZeroOfNeOne h110eq
      have h110eqb : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 110) = 0 := by
        rw [ba.hx1]; exact h110eqz
      by_cases h116one : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 1
      · have h116b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 116) = 1 := by
          rw [ba.hx1]; exact h116one
        let leaf := hcontRunLeafAt_56Else hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k
          ba.b.x1 hInvS ba.b.h8c root0 hk h110b h116b h110eqb
        have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
            (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
            (ContTailStartC C) leaf.ss 5 :=
          c56ElseSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
            (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl
            ba.b.h8c h110b h116b h110eqb
        exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem ba.b
          leaf hSpan (by decide)
      · have h116z : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 0 :=
          bitZeroOfNeOne h116one
        have h116b : evalICmp .slt ba.b.x1 (BitVec.ofNat 8 116) = 0 := by
          rw [ba.hx1]; exact h116z
        by_cases h116eq : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 1
        · have h116eqb : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 116) = 1 := by
            rw [ba.hx1]; exact h116eq
          let leaf := hcontRunLeafAt_58True hc.seam cl ba.b.b35 ba.b.ix ba.b.v ba.b.k
            ba.b.x1 hInvS ba.b.h8c root58T hk h110b h116b h116eqb
          have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
              (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
              (ContTailStartC C) leaf.ss 4 :=
            c58TrueSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
              (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl
              ba.b.h8c h110b h116b h116eqb
          exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem
            ba.b leaf hSpan (by decide)
        · have h116eqz : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0 :=
            bitZeroOfNeOne h116eq
          have h116eqb : evalICmp .eq ba.b.x1 (BitVec.ofNat 8 116) = 0 := by
            rw [ba.hx1]; exact h116eqz
          let leaf := hcontRunLeafAt_58Else hc cl ba.b.b35 ba.b.ix ba.b.v ba.b.k
            ba.b.x1 hInvS ba.b.h8c root0 hk h110b h116b h116eqb
          have hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
              (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1)
              (ContTailStartC C) leaf.ss 5 :=
            c58ElseSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
              (contRunLeafS G C cl ba.b.b35 ba.b.ix ba.b.v ba.b.k ba.b.x1) hInvS rfl
              ba.b.h8c h110b h116b h116eqb
          exact hcontRunArmAt hc hInv hblock hk r hws skip q5 4 hPrefix (by decide) hmem
            ba.b leaf hSpan (by decide)

/-! ### The plain-value class's three non-whitespace byte classes

`.value` is the tag test's `1` arm, and the class's document row fixes its four pivots and
the byte before the entry's end.  Its producer `hcontArm_scalar_of_class` takes a
`HcontScalarPrefix`, which `hcontScalarPrefix_of_inv` derives from the invariant and the
lane row — so this is the branch the class case runs at the three non-whitespace byte
classes, with no supply beyond the payload's `defaultLane` and the class's `scalar` row.
The whitespace byte is `.scalarRun`'s (`hcontArm_scalarRun_of_class`), so the whole cell
`.value` × `HcontByteClass` is produced. -/

/-- **The plain-value class's arm, from the payload's lane and the class's rows.**  The
prefix is `hcontScalarPrefix_of_inv`'s at the class's four bits and the row's lane, and the
seam's three calls are `HcontClassRows.scalar`'s at that prefix's own byte route. -/
theorem hcontArm_value_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx : x = hlastByte G C := hlastByte_of_reg8 hInv h8
  -- the lane's read at the prefix's own state: the route binds registers only
  have hmem : (scS₅ s x (hlastIncV C) (hlastNepV G)).mem = s.mem := rfl
  have hread : readBytes (scS₅ s x (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes r.v.toNat 4) := by
    rw [hmem, cont_inc_toNat G C hk]
    exact r.hread
  exact hcontArm_scalar_of_class hInv hblock hk
    (hcontScalarPrefix_of_inv G C s hInv hk hx h44 h58 hne44 hbit hread r.hvle r.hugt
      (HcontHeadByte.toRoute rfl hb)) hc

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.HcontRunLeaf.cA_of_imm
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeafAt_letters
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeafAt_fLetter
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeafAt_56True
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeafAt_56Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeafAt_58True
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeafAt_58Else
#print axioms LeanLLVM.Refinement.WalkScope.contRunCheck_env8
#print axioms LeanLLVM.Refinement.WalkScope.contRunCheck_idx
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunHeadCells_of_prefix
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunCheckCells_of_head
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunBody_of_skip
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRow_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunArmAt
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_value_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_defaultValueLow
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_defaultValueMid
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_otherValue
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_defaultValueBracket
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_defaultValueBrace
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_defaultValueBracketHigh

end WalkScope
end LeanLLVM.Refinement
