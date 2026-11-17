/-
# The default arm's spans, from the staging

`HcontArm.letters`/`.fLetter`/`.classC` (`JsonStage2WalkDispatchHcontArms`) and their
`LastEntryArm` twins (`JsonStage2WalkDispatchArms`) are the head switch's default arm: the
bytes below `110` in the signed order, split into the `'f'` leaf and the rest, and the class
`110 … 125` whose span is the byte's own.  This module produces all six at every state that
carries the invariant, and composes each into its level's dispatch.

## The class is a field or a range, so `h8` is not a literal

The producers above this tier take the class's byte test at a **literal** — a one-bit
`eq` — and pin the arm's byte with `eq_bit_value`.  These three arms' census classes are
not literals: `.letters` is the range `slt %8 110 = 1` beside `%8 ≠ 102`, `.fLetter` is
that range beside `%8 = 102`, and `.classC` is `slt %8 110 = 0` beside
`slt %8 125 = 1 ∨ %8 = 125`.  The arm's `h8` is `evalOperand s (.reg "%8") = some (.int 8
x)` at a **variable** byte, so the demotion has to run the other way: the class's own
predicate holds of `x`, and the register witness (`WalkInv.iter.reg8`, whose cell is
`hlastByte G C`) supplies the cell once `x` is named as that byte.

`cont_reg8_at` is that lemma, stated once for all three: `cont_reg8`'s cell read at a byte
the class names, the variable-byte form of what `eq_bit_value` does at a literal.
`hlastByte_of_reg8` is its inverse, which is what a wrapper holding the cell at a literal
byte has in hand.  The class's own predicate is a conjunction — the byte's identity with
`hlastByte` and the census's two or three tests — and a producer takes it in one piece.

| arm | the class's own predicate | where `h8` comes from |
|---|---|---|
| `.letters` | `x = hlastByte G C`; the tag test clear; `slt x 110 = 1`; `eq x 102 = 0` | `cont_reg8_at` at the identity |
| `.fLetter` | the same, with `eq x 102 = 1` in place of the clear bit | the same |
| `.classC` | `x = hlastByte G C`; `slt x 110 = 0`; `slt x 125 = 1 ∨ eq x 125 = 1` | the same |

## The rows each arm still takes, and why

`JsonStage2WalkTerminalPrice` marks these arms **D** for the byte and its class bits, the
head segment's endpoint cells and the tail's; the producers confirm the *derivation* and
name what remains.  Nothing about the class's bits is derivable from `WalkInv`: the
invariant says the register holds the head's byte, and which byte that is is the
document's.  So the predicate is supplied and `h8` is derived from it — exactly the split
`eq_bit_value`'s arms have, one level up.

| row | mark | how the producer has it |
|---|---|---|
| `h8` | **D** | `cont_reg8_at` at the class's own identity (`WalkInv.iter.reg8`) |
| the class's tests (`hbit`, `h110`, `hne102`/`h102`, `h125`) | **F** the byte, **D** given it | The census is right that the tests are a function of the head byte; what no lemma supplies is the byte, because the class is a range rather than a literal.  So the producer takes the predicate in one piece — the byte named as `hlastByte G C` beside its tests — and `h8` follows from the naming.  At a literal class the same row is one `eq_bit_value` away |
| `hHead` (the head's chain to `if.else387.i`) | **F** (the arm's own field) | the four pivots pick different blocks per byte class, so the chain is the class's own; it enters as a counted `WalkSegment` at the class's count, with the bound the level's longest class sets (`nH ≤ 12` continuing, `nH ≤ 11` at the last entry) |
| `hm`/`hmk`/`h8m` (the head segment's endpoint) | **F** (the arm's own field) | the endpoint's block, index and byte are the segment's, not the invariant's at `s` |
| `hSpan`/`hs`/`hnS` (`.classC` only) | **F** (the arm's own field) | the span is the byte's own leaf (`c56TrueSpan`, `c56ElseSpan`, `c58TrueSpan`, `c58ElseSpan`) at `nS ≤ 5` |
| `hTail` (the tail's three calls) | **F** (the arm's own field) | the three callees' preconditions and answers at their own argument lists |
| `ht`/`htk`/`htok` (the tail's endpoint) | **F** (the arm's own field) | the tail segment's |
| the level | **F-split** | which side of the count the state is on is the dispatch's hypothesis (`hk` continuing, `hnot` at the last entry); the arm carries nothing about it |

So each producer derives exactly one field — the byte — and takes the rest as premises
named per arm in its own signature.  That is the tier's whole content: the arms existed
only at documents, and the byte is the one field the invariant settles.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The register's byte, at a byte the class names

`eq_bit_value` demotes a literal equality test to a byte equality.  A class that is a
range or a field has no literal, so its demotion is the other direction: the byte is the
register's witness, and the cell follows from naming it. -/

/-- **`%8`'s cell at the class's own byte.**  `cont_reg8`'s cell read at `x` rather than at
`hlastByte G C`, which is what a producer takes when the arm's byte is a field: the
invariant supplies the witness and the class's predicate names the byte. -/
theorem cont_reg8_at {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C) :
    evalOperand s (.reg "%8") = some (.int 8 x) := by
  rw [hx]
  exact cont_reg8 hInv

/-- **The class's byte is the register's witness.**  `cont_reg8_at`'s inverse: a state whose
`%8` cell holds the literal `x` has `x` as the head byte, because the invariant names the
cell at `hlastByte G C`.  A wrapper holding a document's byte composes the two. -/
theorem hlastByte_of_reg8 {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {x : BitVec 8}
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) : x = hlastByte G C := by
  have h1 : lookupName s.env "%8" = some (.int 8 x) := by
    simpa only [evalOperand] using h8
  have h := Option.some.inj (hInv.iter.reg8.symm.trans h1)
  simpa using h.symm

/-! ### The letters route

The class is `slt %8 110 = 1` beside `%8 ≠ 102`, on the scan-free continuation: the span
below `if.else387.i` is `lettersSpan`'s four links at kind `0`, the head's chain is twelve
links at a continuing entry and eleven at the last, and the tail's three calls end at
`if.end473.i` on their empty arm.

**The head's count is the head-switch class's**, not this producer's: twelve at the
bracket-and-mid classes and **eleven** at `.defaultValueLow` (the low bytes and every byte
above `127`), whose route is `NodeBlock5 → LeafBlock → sw.default.i`.  The per-class chains
are `JsonStage2WalkDispatchLettersHead`'s (`contLowHeadSeg` at eleven, `contMidHeadSeg`,
`contOthHeadSeg`, `contBrkHeadSeg`, `contBhHeadSeg` at twelve).  The producer below takes
the segment at the class's own count `nH` with `nH ≤ 12`, so it applies wherever the class's
chain is supplied. -/

/-- **The letters arm on the continuing head, from the staging.**  `HcontArm.letters` at
every state that carries the invariant, with the class's own predicate at the register's
byte: `h8` is `cont_reg8_at`'s, and the head segment, its endpoint cells, the tail and the
merge's cells are the arm's own fields, taken as they are stated. -/
def hcontArm_letters_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .letters (cont_reg8_at hInv hx) hbit h110 hne102 hHead hnH hm hmk h8m hTail ht htk htok

/-- **The letters arm at the last entry, from the staging.**  The same class and the same
fields at the level whose head chain is one link shorter; which side of the count the state
is on is the dispatch's hypothesis, so the arm itself is the continuing one's shape. -/
def lastEntryArm_letters_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .letters (cont_reg8_at hInv hx) hbit h110 hne102 hHead hnH hm hmk h8m hTail ht htk htok

/-- **The letters continuing dispatch, from the staging.** -/
theorem walkDispatch_at_letters_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_letters_of_staging C s hInv hx hbit h110 hne102 hHead hnH hm hmk h8m
      hTail ht htk htok)

/-- **The letters last-entry dispatch, from the staging.**  The level's negated count, at
the arm the producer above inhabits. -/
theorem walkDispatch_at_letters_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_letters_of_staging C s hInv hx hbit h110 hne102 hHead hnH hm hmk h8m
      hTail ht htk htok)

/-! ### The `'f'` leaf

The same range with the leaf's equality **set** rather than clear: the span is `fSpan`'s
four links at kind `9`, and the two segments are the class's own exactly as the letters
route's are. -/

/-- **The `'f'` arm on the continuing head, from the staging.** -/
def hcontArm_fLetter_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .fLetter (cont_reg8_at hInv hx) hbit h110 h102 hHead hnH hm hmk h8m hTail ht htk htok

/-- **The `'f'` arm at the last entry, from the staging.** -/
def lastEntryArm_fLetter_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .fLetter (cont_reg8_at hInv hx) hbit h110 h102 hHead hnH hm hmk h8m hTail ht htk htok

/-- **The `'f'` continuing dispatch, from the staging.** -/
theorem walkDispatch_at_fLetter_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_fLetter_of_staging C s hInv hx hbit h110 h102 hHead hnH hm hmk h8m
      hTail ht htk htok)

/-- **The `'f'` last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_fLetter_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    {x : BitVec 8} (hx : x = hlastByte G C)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_fLetter_of_staging C s hInv hx hbit h110 h102 hHead hnH hm hmk h8m
      hTail ht htk htok)

/-! ### The class-C span

The class is `110 … 125`: `slt %8 110 = 0` beside `slt %8 125 = 1 ∨ %8 = 125`.  Its span is
the byte's own leaf — `110` through `LeafBlock56`'s true arm, `111 … 115` through its else
arm, `116` from `LeafBlock58` itself, `117 … 125` through its else arm — so the segment is
`Seg` at `nS ≤ 5` rather than one composition, and it enters beside the head's chain and the
tail's three calls.  `126`/`127` are excluded by the upper premise; they are `.ws`'s and
`.cleanup`'s. -/

/-- **The class-C arm on the continuing head, from the staging.**  The byte's own span
enters as the arm's field, at the class's four routes' count `nS ≤ 5`. -/
def hcontArm_classC_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .classC (cont_reg8_at hInv hx) h110 h125 hHead hnH hm hmk h8m hSpan hs hnS
    hTail ht htk htok

/-- **The class-C arm at the last entry, from the staging.** -/
def lastEntryArm_classC_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) {x : BitVec 8} (hx : x = hlastByte G C)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .classC (cont_reg8_at hInv hx) h110 h125 hHead hnH hm hmk h8m hSpan hs hnS
    hTail ht htk htok

/-- **The class-C continuing dispatch, from the staging.** -/
theorem walkDispatch_at_classC_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_classC_of_staging C s hInv hx h110 h125 hHead hnH hm hmk h8m hSpan hs hnS
      hTail ht htk htok)

/-- **The class-C last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_classC_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_classC_of_staging C s hInv hx h110 h125 hHead hnH hm hmk h8m hSpan hs hnS
      hTail ht htk htok)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cont_reg8_at
#print axioms LeanLLVM.Refinement.WalkScope.hlastByte_of_reg8
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_letters_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_letters_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_letters_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_letters_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_fLetter_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_fLetter_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_fLetter_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_fLetter_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_classC_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_last_of_staging

end WalkScope
end LeanLLVM.Refinement
