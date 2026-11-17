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
| the letters route (`LetS413`) | `contWsTailStart …` | `0` | `scan` |
| `'f'` (`FS413`) | `FS413 (contWsSeamS …)` | `9` | `scanF` |
| `110` (`ClsS413T`) | `ClsS413T (contWsSeamS …)` | `10` | `scan56True` |
| `111 … 115` (`ClsS413F`) | `contWsTailStart …` | `0` | `scan`, cast |
| `116` (`ClsS58T`) | `ClsS58T (contWsSeamS …)` | `8` | `scan58True` |
| `117 … 125` (`HeadS413`) | `contWsTailStart …` | `0` | `scan`, cast |

**Which of those items are genuinely new.**  `scanF`, `scan56True` and `scan58True` are:
their leaves' predecessors are `if.then397.i`, `if.then403.i` and `LeafBlock58`, whose
`phi` incomings are `9`, `10` and `8`, and a cast of the `0` seam's rows would keep `0`
(`HcontSeamCalls.cast` preserves `cA`) and could not discharge the leaf's `hval`
(`HcontRunLeaf.cA_of_imm` states exactly that the leaf pins its seam's literal).  The
three kind-`0` leaves are **not** new supply: their seam is the one state
`contWsTailStart` builds — `if.else405.i`'s edge — the leaf's span leaves that state for
the carry the leaf binds, and the rows mention only the memory, the counter and the
carry's stage, so one item serves all three by `HcontSeamCalls.cast`.

## The row at each leaf

`HcontClassRows.runRow` (`JsonStage2WalkDispatchClassRows`) is the run class's row: the
class's prefix to `sw.default.i`, the shared four's cells, the check state's rows, the
run's body and the byte's leaf.  Its leaf is its argument, so a producer of the row is a
producer *at a leaf*: `hcontRunRowAt_letters` … `_58Else` below are those, each building
the row from the class's rows and the leaf's own supply.  What they do not supply is the
row's remaining data — the prefix and the check state's document rows — which
`HcontClassRows.runRow` states as its own obligation; the composition here is what the
class case needs at a whitespace document byte, and it is stated per leaf so no cell of the
two-dimensional split (head class × `HcontByteClass`) is missing a row.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassCase

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

/-! ### The letters route's leaf: the seam's `scan` item -/

/-- **The letters route's leaf, from the seam's rows.**  `lettersSpan` ends at `LetS413`,
whose predecessor is `if.else405.i` — `scan`'s own seam — so the item serves it directly
and no new supply is taken. -/
noncomputable def hcontRunLeafAt_letters {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hs : HcontSeamAbi G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hs.scan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_letters G C sl b35 ix v k x1 hInvS h8 (hs.scan C sl b35 ix v k x1).calls
    (hs.scan C sl b35 ix v k x1).hcA hroot0 hk h110 hne102

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

/-! ### `111 … 115`'s leaf: the `scan` item, cast -/

/-- **`111 … 115`'s leaf, from the shared seam rows.**  `c56ElseSpan` ends at `ClsS413F`,
whose predecessor is `if.else405.i`; the rows are `scan`'s, cast across the leaf's binds by
`hcontRunLeaf_56Else`, and no new supply is taken. -/
noncomputable def hcontRunLeafAt_56Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hs : HcontSeamAbi G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hs.scan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_56Else G C sl b35 ix v k x1 hInvS h8 (hs.scan C sl b35 ix v k x1).calls
    (hs.scan C sl b35 ix v k x1).hcA hroot0 hk h110 h116 h110eq

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

/-! ### `117 … 125`'s leaf: the `scan` item, cast -/

/-- **`117 … 125`'s leaf, from the shared seam rows.**  `c58ElseSpan` ends at `HeadS413`,
whose predecessor is `if.else405.i`; the rows are `scan`'s, cast by
`hcontRunLeaf_58Else`, and no new supply is taken.  This is the leaf the earlier revision
pinned the whole bundle to. -/
noncomputable def hcontRunLeafAt_58Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (hs : HcontSeamAbi G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hs.scan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_58Else G C sl b35 ix v k x1 hInvS h8 (hs.scan C sl b35 ix v k x1).calls
    (hs.scan C sl b35 ix v k x1).hcA hroot0 hk h110 h116 h116eq

/-! ### The run's row at each leaf

`HcontClassRows.runRow` is the row, with the leaf as its argument; each producer below
applies it at one leaf, built from that leaf's own supply item.  The row's other data —
the class's prefix to `sw.default.i`, the shared four's cells and the check state's
document rows — is `runRow`'s own obligation, stated where the row is stated. -/

/-- **The run's row at the letters leaf.** -/
noncomputable def hcontRunRowAt_letters {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 0) :
    HcontRunRow G C s :=
  hc.runRow C s hInv hblock hk r hws
    (hcontRunLeafAt_letters hc.seam sl b35 ix v k x1 hInvS h8 hroot0 hk h110 hne102)

/-- **The run's row at the `'f'` leaf.** -/
noncomputable def hcontRunRowAt_fLetter {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scanF C sl b35 ix v k x1).calls.rdv.toNat 4))
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 1) :
    HcontRunRow G C s :=
  hc.runRow C s hInv hblock hk r hws
    (hcontRunLeafAt_fLetter hc.seam sl b35 ix v k x1 hInvS h8 hroot0 hk h110 h102)

/-- **The run's row at `110`'s leaf.** -/
noncomputable def hcontRunRowAt_56True {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan56True C sl b35 ix v k x1).calls.rdv.toNat 4))
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 1) :
    HcontRunRow G C s :=
  hc.runRow C s hInv hblock hk r hws
    (hcontRunLeafAt_56True hc.seam sl b35 ix v k x1 hInvS h8 hroot0 hk h110 h116 h110eq)

/-- **The run's row at `111 … 115`'s leaf.** -/
noncomputable def hcontRunRowAt_56Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 0) :
    HcontRunRow G C s :=
  hc.runRow C s hInv hblock hk r hws
    (hcontRunLeafAt_56Else hc.seam sl b35 ix v k x1 hInvS h8 hroot0 hk h110 h116 h110eq)

/-- **The run's row at `116`'s leaf.** -/
noncomputable def hcontRunRowAt_58True {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan58True C sl b35 ix v k x1).calls.rdv.toNat 4))
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 1) :
    HcontRunRow G C s :=
  hc.runRow C s hInv hblock hk r hws
    (hcontRunLeafAt_58True hc.seam sl b35 ix v k x1 hInvS h8 hroot0 hk h110 h116 h116eq)

/-- **The run's row at `117 … 125`'s leaf.** -/
noncomputable def hcontRunRowAt_58Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hc : HcontClassRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (r : HcontDefaultRow G C s) (hws : wsStop G (r.v.toNat - 1))
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes (hc.seam.scan C sl b35 ix v k x1).calls.rdv.toNat 4))
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    HcontRunRow G C s :=
  hc.runRow C s hInv hblock hk r hws
    (hcontRunLeafAt_58Else hc.seam sl b35 ix v k x1 hInvS h8 hroot0 hk h110 h116 h116eq)

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
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRowAt_letters
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRowAt_fLetter
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRowAt_56True
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRowAt_56Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRowAt_58True
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRowAt_58Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_value_of_lane

end WalkScope
end LeanLLVM.Refinement
