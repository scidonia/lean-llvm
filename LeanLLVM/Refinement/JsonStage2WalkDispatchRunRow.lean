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

/-- `%8` at the count test's target is `sw.default.i`'s. -/
theorem contSwOut_env8 (q5 : State) (inc nep : BitVec 64) :
    lookupName (contSwOut q5 inc nep).env "%8" = lookupName q5.env "%8" := by
  simp only [contSwOut, State.bind]
  rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%8") _ _ (by decide)]

/-- **The run's body, from the skip's class and the check state's cells.**  The class
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
  -- the prefix endpoint's invariant and its cells
  have hInv5 : WalkInv G (HeadAC₄ C) q5 := hPrefix.inv'
  have hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, hlastIncV]
    exact hInv5.inc_reg
  have hnep : evalOperand q5 (.reg "%nep") = some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, hlastNepV]
    exact hInv5.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
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
  have hugt : evalICmp .ugt (BitVec.ofNat 64 r.v.toNat) (contIx G C) = 1 := r.hugt
  -- the byte before the entry's end, at the suffix's own memory
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
    { q5 := q5
      nq := nq
      hPrefix := hPrefix
      hnq := hnq
      inc := hlastIncV C
      nep := hlastNepV G
      hinc := hinc
      hnep := hnep
      hnext := hnext
      ep := G.ep
      h5 := h5
      hi63 := hi63
      v := r.v
      hread := hread
      ix := contIx G C
      hidx := hidx
      htok := htok
      hgap := hgap
      hugt := hugt
      b35 := contB35 G r.v
      hread35 := hread35
      b := b
      leaf := leaf
      ev := ev
      rows := rows }

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
#print axioms LeanLLVM.Refinement.WalkScope.contSwOut_env8
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunBody_of_skip
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunRow_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_value_of_lane

end WalkScope
end LeanLLVM.Refinement
