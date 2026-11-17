/-
# The continuing census's class case, one branch per class

`HcontClass` (`JsonStage2WalkDispatchHcontArms`) classifies the head byte, and
`HcontClass.complete` proves every byte has a class.  This module states the case's
branches: at each class, the arm the class's producer builds from the payload's rows.

Each branch is one theorem and reads one field of `HcontClassRows`
(`JsonStage2WalkDispatchClassRows`) — that group is the producers' remaining argument
lists, so a branch is the projection of the class's row into the producer the arm was
already proved to need.  Nothing here holds an arm or a bundle: the fields are the seam's
three callee rows with the kind literal and the root slot's word, the class's document row,
and (for the positive-depth opener) the route the arm itself carries.

## The branches

| class | branch | the field it reads |
|---|---|---|
| `.value`, at a scan-free document byte | `hcontArm_scalar_of_class` | `scalar` — the prefix's seam row |
| `.defaultValueHigh`, at a scan-free document byte | `hcontArm_cleanup_of_class` | `cleanupRow`, and `cleanup` for the document row |
| the default arm's scan-free classes | `hcontArm_letters_of_class`, `hcontArm_fLetter_of_class`, `hcontArm_classC_56True_of_class` … `hcontArm_classC_58Else_of_class` | `letters`, `fLetter`, `c56True` … `c58Else` |
| `.run`, the whitespace document byte | `hcontArm_run_of_class` | `run`, with the byte's own leaf below `if.else387.i` as the arm's span |
| `.stringOpener` at `C.sp ≠ 0` | `hcontArm_stringOpenAboveZero_of_class` | `deep`, and the payload's `abi.openCall` |

The classes whose producer is the invariant's own — the four derived delimiters
(`hcontArm_of_derivedClass`) and the container openers
(`walkDispatch_at_open91_of_payload`, `walkDispatch_at_open123_of_payload`) — need no
branch here: their rows are the payload's `abi.openCall` and the invariant's cells, and
they are proved where they are stated.

## What the case still needs

**One half is closed.**  `HcontCleanupFacts` (`JsonStage2WalkRevolution`) no longer asserts
the scan-free bits of the byte before the entry's end: it carries the byte's class
(`hb : HcontByteRoute (cont35 b35)`), states its seam cells at the `NodeBlock41` state every
route leaves them at, and states its tail at the class's own seam
(`contTailStartByte`/`contCleanupEndByte`).  The class's chain is then a theorem per class
— `hcontHeadSegCleanup` is `∃ nH ≤ 12` at whichever leaf `hb` names, and
`hcontSpan17_of_cleanup`/`hcontPrefixCleanupSeg`/`walkRevolutionMergeSeg` carry the class's
own count (`n ≤ 20`, `p ≤ 21`, and the price `p + 2 ≤ 32·Δk`).

**What the leaf classes now hold is the tail, and it is produced at the route.**
`hcontTailByte_of_calls` (`JsonStage2WalkDispatchSegments`) is `hcontTail_of_calls`'s
route-generic twin: it takes `hb : HcontByteRoute (cont35 b35)` and the three callees'
rows at `contTailStartByte … hb`, so the arm-level document row (`HcontCleanupDoc`) and
its chain (`hcontSpan17_of_doc`) are stated at the byte's route too, and the default-value
branch passes `hb` rather than `.scanFree`.  The tail's calls bind no cell the seam's
route changes (`contSeamByte_ee`, `contSeamByte_cond` are stated at every class), so this
is the same producer re-pointed, not a new one.  What `walkContinueFacts_of_payload` still
waits on is the class-case assembly over `HcontClass.complete` at the cells whose rows the
payloads do not carry — the `.ws` arm's `HcontFacts` and the six `.run` cells' document
rows — and not the leaf wiring, which is `JsonStage2WalkDispatchRunRow`'s, nor the
plain-value class's cell, which is `hcontArm_value_of_lane`'s.

**The run's shape no longer restricts the leaf.**  `.run` needed `lettersSpan`
(`LetS413`) or `fSpan` (`FS413`) as its span below `if.else387.i`, and the bundle's tail
and landing were `contWsTailStart`-shaped — `HeadS413`'s binds — so only the class-C else
leaf fitted.  `HcontRunRows`/`HcontRunFacts` now state the tail's source at a leaf `ss`,
its target and every landing field at `ScanEntry ss …`, and carry the four cells
`ScanEntry`/`Latch462S` bind nothing of; `HcontRunRow` takes the leaf, and its arm's span
ends at it.  The six leaves' producers are this module's `hcontRunLeaf_letters` … `_58Else`.
What a producer of the *row* must add is the leaf's three call answers and the landing
built on them: the kind literal is part of the memory the first call reads, so `102`,
`110` and `116` have their own groups (`HcontSeamAbi.scanF`/`scan56True`/`scan58True`) and
the other three cast the seam's (`HcontSeamCalls.cast`).  That wiring is
`JsonStage2WalkDispatchRunRow`'s (`hcontRunLeafAt_letters` … `_58Else`, and the row by
`hcontRunRow_of_rows`); the four continuing seam fields carry their
literal (`HcontSeamKind`), so the three nonzero-kind leaves' supply cannot be cast from the
`0` seam's.  See `hcontRunRow_of_rows` and `hcontArm_run_of_row`.

The byte selection itself is **done**: `JsonStage2WalkDispatchClassTransport` derives the
route's own bits (`slt %8 110`, `eq %8 116`, `slt %8 116`, `eq %8 116`, `slt %8 125` and
the seam's tag test) from each default-value constructor's range bits, builds the
head chain at them, and returns the arm.  Its six branches cover
`.defaultValueLow`, `.defaultValueMid`, `.otherValue`, `.defaultValueBracket`,
`.defaultValueBracketHigh` and `.defaultValueBrace`, including the brace class `124` and
the bracket-high class's `'f'`/letters/class-C split.  So the class case's default-value
half needs no further bit transport — only the class case's assembly and the leaf
bundle above.

**The last level's leaf bundle is closed.**  `HlastFacts` and `HlastResidue` carry the
last byte's route (`hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))`) in place of
the three scan-free bits, `hlastTailByte_of_calls` produces `hTail` at the class's own
seam, `hlast_toMerge` states the path at the route's count (`12 + hlastByteCount hb + 3 +
1 ≤ 20`) and `hlast_finish`/`hlast_refuse` price it at `22 ≤ 32` and `25 ≤ 32`, so
`.highByte` selects `.lowLeaf`/`.highLeaf` rather than assuming the scan-free leaf.

**What the two class cases still need is a payload item, not a proof.**  Each branch
exists, but the continuing case is two-dimensional — the head class does not fix the next
byte's class — and after the route-carrying scalar bundle one cell of that matrix has no
arm at all: `.value` × `wsByte`, the whitespace run after a numeral.

* The head's byte class is `HcontClass`'s; the next entry's last byte's class is
  `HcontByteClass` (from the payload's `defaultLane`).  At the high-byte head (`126`/`127`)
  the two partition the matrix: `HcontByteClass.wsByte` is `HcontArm.ws`'s run
  (`HcontFacts`, whose prefix is that head's) and the three leaves are
  `HcontArm.cleanup`'s (`HcontCleanupFacts` carries the route, so all three).  At the
  default arm's classes (`tag = 0`) they partition it too: `wsByte` is `HcontArm.run`
  (the check state's row, `hcontRunRow_of_rows`, plus the byte's leaf composed from the
  row), and the three leaves are `letters`/`fLetter`/`classC` by the head byte's pivots,
  with the chain built from `defaultLane` plus those bits.
* **`.value` takes the document byte's route, and both of its halves are produced.**
  `HcontArm.scalar` is the plain-value route's scan-free arm (the tag test is `1` there,
  so `letters`/`fLetter`/`classC`, which take `tag = 0`, are excluded), and both the
  document row (`HcontScalarPrefix.hb`) and the bundle (`HcontScalarFacts.hb`) carry
  `hb : HcontByteRoute (cont35 b35)`.  The class's seam row (`HcontClassRows.scalar`) is
  stated at `scSeamByte … pre.hb`, the chain to it is `scSeamSegByte` at
  `hlastByteCount hb`, and the tail is `scTailByte_of_calls` at the same seam, so
  `.value` × {`scanFree`, `lowLeaf`} are produced as well as the high leaf.  The fourth
  cell — `.value` × `wsByte`, the whitespace run after a numeral — is `HcontArm.scalarRun`
  (`JsonStage2WalkHcontWsScalar`): its bundle `HcontScalarWsFacts` is the numeral prefix's
  document cells, the byte's class with the run's stop and its per-index facts, the seam's
  own cells, the tail's segment and the scan's landing; the run is restated at this
  prefix (`scWsRunF`, whose seam is the tag-true link `scWsSeamSeg` rather than the
  class-C span's) and the path to the merge is `walkDispatch_at_continue_scalarWs`, so
  the arm is proved, not supplied.  Its row is `HcontClassRows.scalarRun`
  (`HcontScalarWsRow`, the seam's three calls in place of the tail's segment) and its
  branch is `hcontArm_scalarRun_of_class`, whose producer builds the tail from the calls
  (`scanTailSeg_at`) — so no segment is a premise at that cell either.

**What the last level still needs is a payload item, not a proof** — closed: the last
level's case is total as written, because its `.scalar` is guarded by the document route
the row carries (`HlastScalarRows.hb13/hb32/hbne32`) rather than by a fixed bundle, and
its default arm splits on `wsStop` before choosing a leaf, so every cell of its matrix has
a branch.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassCLeaves
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontStringDeep
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The plain-value class -/

/-- **The plain-value class's continuing arm, from the class's row.**  The class's producer
is `hcontArm_scalar_of_rows`; its remaining inputs are the seam's three callee rows, the
kind literal and the root slot's word, which `HcontClassRows.scalar` carries at the class's
own prefix. -/
theorem hcontArm_scalar_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (pre : HcontScalarPrefix G C s) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.scalar C s pre
  exact hcontArm_scalar_of_rows hInv hblock hk pre calls hcA hroot

/-! ### The plain-value class's whitespace run -/

/-- **The whitespace-run cell's continuing arm, from the class's row.**  The row is
`HcontScalarWsRow`'s — the prefix's document cells, the byte's class with the run's stop,
the seam's cells and the seam's three calls — and the arm's producer builds the tail from
the calls (`hcontArm_scalarRun_of_row`), so neither a segment nor a bundle is a premise
here. -/
theorem hcontArm_scalarRun_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) :=
  ⟨hcontArm_scalarRun_of_row hInv hblock hk (hc.scalarRun C s hInv hblock hk)⟩

/-! ### The default arm's scan-free classes -/

/-- **The letters class's continuing arm, from the class's row.**  The head chain is the
caller's (the class's own count and endpoint); the seam's three callee rows, their kind
literal `0` and the root slot's word are the row's. -/
theorem hcontArm_letters_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.letters C s ch
  exact hcontArm_letters_of_rows hInv hk h8 hbit h110 hne102 ch calls hcA hroot

/-- **The `'f'` leaf's continuing arm, from the class's row.** -/
theorem hcontArm_fLetter_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.fLetter C s ch
  exact hcontArm_fLetter_of_rows hInv hk h8 hbit h110 h102 ch calls hcA hroot

/-- **`110`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_56True_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c56True C s ch
  exact hcontArm_classC_56True_of_rows hInv hk h8 h110 h116 h110eq h125 ch calls hcA hroot

/-- **`111 … 115`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_56Else_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c56Else C s ch
  exact hcontArm_classC_56Else_of_rows hInv hk h8 h110 h116 h110eq h125 ch calls hcA hroot

/-- **`116`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_58True_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c58True C s ch
  exact hcontArm_classC_58True_of_rows hInv hk h8 h110 h116 h116eq h125 ch calls hcA hroot

/-- **`117 … 125`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_58Else_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c58Else C s ch
  exact hcontArm_classC_58Else_of_rows hInv hk h8 h110 h116 h116eq h125 ch calls hcA hroot

/-! ### The default-value class -/

/-- **The default-value route's arm, from the class's rows.**  The document row is produced
from the payload's own default row (`hcontCleanupDoc_of_lane`) at the byte's route, and the
seam's three callee rows are the class's; the root slot's word is the state's own, so the
arm is total over it. -/
theorem hcontArm_cleanup_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontByteRoute (cont35 (contB35 G r.v)))
    (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  let doc := hcontCleanupDoc_of_lane hk r hb
  obtain ⟨calls, hcA, hroot⟩ := hc.cleanupRow C s doc
  exact hcontArm_cleanup_of_rows hInv hblock hk hlt125 hne125 doc hroot calls hcA rfl

/-! ### The run class's leaves

`if.then413.i` is reached through six leaves — the letters pivot's two arms, `LeafBlock56`'s
two and `LeafBlock58`'s two — and each of them is a `HcontRunLeaf`: its endpoint, the
endpoint's invariant (its own span's), the tail's three call rows at it, the root slot's
word, and its `phi`'s predecessor with the kind literal it selects.

The three leaves whose predecessor is `if.else405.i` (kind `0`) take the seam's rows and
`HcontSeamCalls.cast` them to their own state: the leaves bind cells only, so their memory
and counter are the seam's.  The other three cannot: the kind literal is part of the memory
the first call reads (`s2ValuePosPre`'s `writeBytes … (natToBytes cA.toNat 4)`), so a leaf
with `if.then403.i`'s `10`, `if.then397.i`'s `9` or `LeafBlock58`'s `8` has its own group —
`HcontSeamAbi.scan56True`/`scanF`/`scan58True`.  A cast that kept the seam's `0` could not
discharge the leaf's own `phi` (`hop`: the operand the leaf's edge selects *is* the kind).

Each producer is stated at the run's own terms, so the state is
`contWsSeamS C (wsSlAt G sl b35 ix v k) k x1` — the seam `if.end372.i` leaves. -/

/-- The run's seam state, at the terms the six leaves are stated at. -/
abbrev contRunLeafS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8) : State :=
  contWsSeamS C (wsSlAt G sl b35 ix v k) k x1

/-- **A run leaf, from its span and its own call rows.**  The common body of the six
producers: the span's endpoint invariant is the leaf's, the root slot's word is the
stream's transported across the kind store (`classCSeam_rootRead`), and the carry's two
bounds are the seam's (`if.else387.i` emits nothing). -/
noncomputable def hcontRunLeaf_of_span {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {sm ss : State} {nS : Nat}
    (hspan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C) sm (ContTailStartC C) ss nS)
    (hss : ss.mem = sm.mem)
    (hInvS : WalkInv G (ContSeamC C) sm) (hk : C.k + 1 < G.nep)
    (calls : HcontSeamCalls G (ContTailStartC C) ss)
    (hroot0 : readBytes sm.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4))
    (pT : String) (hpre : ss.pre = some pT) (op : Operand)
    (hphi : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hval : evalOperand (stateAt ss.env ss) op = some (.int 32 calls.cA)) :
    HcontRunLeaf G C where
  ss := ss
  hInv := hspan.measure.inv'
  calls := calls
  hroot := classCSeam_rootRead (C := ContTailStartC C) (sm := sm) (ss := ss) hss calls.cA
    calls.rdv hroot0
  htight := hInvS.events_le_of_tight
    (walkEmitC_of_not_contains (b := "if.else387.i") (by decide))
  hklt := by show C.k < G.nep; omega
  pT := pT
  hpre := hpre
  op := op
  hphi := hphi
  hval := hval

/-- **The letters leaf's run data**: `LetS413`, kind `0`, from the seam's rows. -/
noncomputable def hcontRunLeaf_letters {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_of_span G C
    (lettersSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C sl b35 ix v k x1) hInvS rfl h8 h110 hne102)
    (by simp [LetS413, LetS405, LetS54, HeadS62, State.bind])
    hInvS hk
    (calls.cast (s := contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)
      (s' := LetS413 (contRunLeafS G C sl b35 ix v k x1) x1) rfl rfl)
    hroot0 "if.else405.i" rfl
    (.imm (.int 32 (BitVec.ofNat 32 0))) clsC_phi_else405
    (by simp only [HcontSeamCalls.cast, hcA, evalOperand, Const.toValue])

/-- **The `'f'` leaf's run data**: `FS413`, kind `9`, from its own rows. -/
noncomputable def hcontRunLeaf_fLetter {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (calls : HcontSeamCalls G (ContTailStartC C) (FS413 (contRunLeafS G C sl b35 ix v k x1) x1))
    (hcA : calls.cA = BitVec.ofNat 32 9)
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x1 (BitVec.ofNat 8 102) = 1) :
    HcontRunLeaf G C :=
  hcontRunLeaf_of_span G C
    (fSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C sl b35 ix v k x1) hInvS rfl h8 h110 h102)
    (by simp [FS413, FS397, LetS54, HeadS62, State.bind])
    hInvS hk calls hroot0 "if.then397.i" rfl
    (.imm (.int 32 (BitVec.ofNat 32 9))) (by decide)
    (by simp only [hcA, evalOperand, Const.toValue])

/-- **`110`'s leaf's run data**: `ClsS413T`, kind `10`, from its own rows. -/
noncomputable def hcontRunLeaf_56True {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (calls : HcontSeamCalls G (ContTailStartC C)
      (ClsS413T (contRunLeafS G C sl b35 ix v k x1) x1))
    (hcA : calls.cA = BitVec.ofNat 32 10)
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 1) :
    HcontRunLeaf G C :=
  hcontRunLeaf_of_span G C
    (c56TrueSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C sl b35 ix v k x1) hInvS rfl h8 h110 h116 h110eq)
    (by simp [ClsS413T, ClsS403, ClsS56, HeadS60, HeadS62, State.bind])
    hInvS hk calls hroot0 "if.then403.i" rfl
    (.imm (.int 32 (BitVec.ofNat 32 10))) clsC_phi_then403
    (by simp only [hcA, evalOperand, Const.toValue])

/-- **`111 … 115`'s leaf's run data**: `ClsS413F`, kind `0`, from the seam's rows. -/
noncomputable def hcontRunLeaf_56Else {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x1 (BitVec.ofNat 8 110) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_of_span G C
    (c56ElseSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C sl b35 ix v k x1) hInvS rfl h8 h110 h116 h110eq)
    (by simp [ClsS413F, ClsS405, ClsS56, HeadS60, HeadS62, State.bind])
    hInvS hk
    (calls.cast (s := contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)
      (s' := ClsS413F (contRunLeafS G C sl b35 ix v k x1) x1) rfl rfl)
    hroot0 "if.else405.i" rfl
    (.imm (.int 32 (BitVec.ofNat 32 0))) clsC_phi_else405
    (by simp only [HcontSeamCalls.cast, hcA, evalOperand, Const.toValue])

/-- **`116`'s leaf's run data**: `ClsS58T`, kind `8`, from its own rows. -/
noncomputable def hcontRunLeaf_58True {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (calls : HcontSeamCalls G (ContTailStartC C)
      (ClsS58T (contRunLeafS G C sl b35 ix v k x1) x1))
    (hcA : calls.cA = BitVec.ofNat 32 8)
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 1) :
    HcontRunLeaf G C :=
  hcontRunLeaf_of_span G C
    (c58TrueSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C sl b35 ix v k x1) hInvS rfl h8 h110 h116 h116eq)
    (by simp [ClsS58T, HeadS58, HeadS60, HeadS62, State.bind])
    hInvS hk calls hroot0 "LeafBlock58" rfl
    (.imm (.int 32 (BitVec.ofNat 32 8))) clsC_phi_leaf58
    (by simp only [hcA, evalOperand, Const.toValue])

/-- **`117 … 125`'s leaf's run data**: `HeadS413`, kind `0`, from the seam's rows.  This is
the leaf the bundle was pinned to before the parameterisation; it stays as the instance the
`HcontWsSeam` group feeds (`hcontRunLeaf_of_seam`). -/
noncomputable def hcontRunLeaf_58Else {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (hInvS : WalkInv G (ContSeamC C) (contRunLeafS G C sl b35 ix v k x1))
    (h8 : evalOperand (contRunLeafS G C sl b35 ix v k x1) (.reg "%8") = some (.int 8 x1))
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot0 : readBytes (contRunLeafS G C sl b35 ix v k x1).mem (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4))
    (hk : C.k + 1 < G.nep)
    (h110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    HcontRunLeaf G C :=
  hcontRunLeaf_of_span G C
    (c58ElseSpan (calls := stage2Calls stage2SubCalls) G (ContSeamC C)
      (contRunLeafS G C sl b35 ix v k x1) hInvS rfl h8 h110 h116 h116eq)
    (by simp [HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, State.bind])
    hInvS hk calls hroot0 "if.else405.i" rfl
    (.imm (.int 32 (BitVec.ofNat 32 0))) clsC_phi_else405
    (by simp only [hcA, evalOperand, Const.toValue])

/-! ### The run class -/

/-- **The run class's continuing arm, from the class's row.**  The row is `HcontRunRow`'s —
the prefix, the check state's rows and the seam's group — and the span is the head byte's
own leaf below `if.else387.i`, which the caller composes from the class's bits.  The bundle
is the row's consequence (`hcontRunFacts_of_seam`), not a premise. -/
theorem hcontArm_run_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (row : HcontRunRow G C s) {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C) row.seamS
      (ContTailStartC C) row.tailS nS)
    (hnS : nS ≤ 5) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) :=
  hc.run C s hInv hblock hk row hSpan hnS

/-! ### The string opener above depth zero -/

/-- **The positive-depth opener's arm, from the class's row.**  The class's own facts are
derived — the byte from `cont_reg8`, the two stack bytes from the carry's maps, the call's
staging and answer from `HcontOpenCall` — and the route is the row: the merge's counted
segment or the refusal's witness.  So the arm the class takes is exactly the route the
state's own memory and stack bytes select, and nothing the arm establishes is assumed. -/
def hcontArm_stringOpenAboveZero_of_class {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) (hsp : C.sp ≠ 0)
    (hp : HcontPayload G) (hc : HcontClassRows G) :
    HcontArm (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨rdv, _hread, hpreV, r, hcall⟩ := hp.abi.openCall C s hInv hblock hk
  cases hc.deep C s hInv hblock hk h34 hsp with
  | merge Cd sd p k2 nepv hseg hblockD hkC prev hprev hpre hinc hnepv hadvance hcap hprice =>
    exact hcontArm_stringOpenAboveZeroMerge_of_staging C s hInv h34 hsp hpreV r hcall
      Cd sd p k2 nepv hseg hblockD hkC prev hprev hpre hinc hnepv hadvance hcap hprice
  | refuse href =>
    exact hcontArm_stringOpenAboveZeroRefuse_of_staging hInv h34 hsp hpreV r hcall href

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_of_span
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_letters
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_fLetter
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_56True
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_56Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_58True
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_58Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_letters_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_fLetter_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_56True_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_56Else_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_58True_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_58Else_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_stringOpenAboveZero_of_class

end WalkScope
end LeanLLVM.Refinement
