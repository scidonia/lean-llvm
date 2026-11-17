/-
The continuing entry's scalar arm: the plain-value token with no whitespace run.

## Why this arm exists

`HcontCase` (`JsonStage2WalkDispatchWitnessString`) as it stands has three arms: the
whitespace token and the scan-free token, both of which require the head byte to be `126`
or `127` (`hlt125`/`hne125`), and the standalone string, which requires the byte to be
`34`.  The continuing branch's premise (`WalkContinueFacts`) is asked at every head state
with an entry left, so `JsonStage2WalkHcontDomain` refutes the old split at the document
`"01"`: byte `0x30`, a numeral at a non-last entry, satisfies no arm.  The head switch
sends it to `sw.default.i` through `NodeBlock5 → NodeBlock → LeafBlock1`, and the tag test
at its token's end takes the plain-value arm — a *different* route from the high bytes'
`NodeBlock19 → NodeBlock17 → LeafBlock15 → … → NodeBlock62`, and one no bundle described.

This module states that route's own bundle and composition:

| piece | links |
|---|---|
| the head: `NodeBlock21`, `NodeBlock5`, `NodeBlock`, `LeafBlock1` | 4 |
| `sw.default.i`'s count test's succeeding arm, `cond.true345.i`, `cond.end349.i`'s bound | 3 |
| the whitespace check: `land.lhs.true357.i`, `NodeBlock41`, `NodeBlock39`, `LeafBlock37` | 4 |
| the token's end `if.end372.i`, on its tag test's *true* arm | 1 |
| the tail's three calls, on the empty arm | 3 |
| the merge | 1 |

`4 + 3 + 4 + 1 = 12` links to `if.then413.i`; the scan-free tail's three and the merge's
step make `16`.  At a continuing entry `Δk = 1` and the byte term is the entry's span, so
the price `16 + 2 = 18` sits inside the entry allowance `32`.

## What is stated, and what the arm shares

The route is the *no-whitespace* class: the byte before the entry's end is at or above
`32` in the signed order and is not `32` itself, so the whitespace check takes
`LeafBlock37`'s else arm and the token ends at the entry's end.  The tail is then the one
`consumerTailSegEmptyAt` (`JsonStage2WalkPrefixCount`) composes, stated at its entry state
with the kind operand the `if.end372.i` edge selects — `7` here, `0` on the letters' route
— which is exactly how the last entry's plain-value arm shares the same three links
(`JsonStage2WalkDispatchScalarPrefix`).

The states are `def`s, one per link, because a `WalkSegment` threads states by name; the
cells the whitespace check and the seam read (`%35`, `%8`, `%cond350.i`, `%ee.1.i`,
`%end.i`) each have a peel here, and the static registers are `WalkInv.regs` at each
link's own source.  So the bundle's premises are the document's byte class, the entry
stream's lane, the tail's callee preconditions and the tag bit — not a segment.

## The memory is the high-byte arm's

`cond.end349.i` writes the token record twice and the lane load and the zero-extension
write nothing, so this route's `cond.end349.i` target has the *same* memory as the
high-byte route's: `sEnd_mem` is the `rfl` that says so, and the document's byte before
the entry's end is therefore `cont_hread35`'s (`JsonStage2WalkHcontFactsOfStaging`) at
this bundle's own witness.  That is the one fact the two routes share, and stating it as
an equation rather than re-deriving the read keeps the byte's producer single.
-/
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg
import LeanLLVM.Refinement.JsonStage2WalkHcontFactsOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarPrefix

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The carries, named

One per link, on the previous link's carry.  The head's four pivots are the scalar arm's
(`NodeBlock5 → NodeBlock → LeafBlock1`), and the count test's *succeeding* arm puts
`cond.true345.i` between `sw.default.i` and `cond.end349.i`. -/

/-- `NodeBlock5`'s carry: `%8 < 91` holds. -/
abbrev Scc₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock5" }

/-- `NodeBlock`'s carry: `%8 < 44` does not hold. -/
abbrev Scc₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₁ C with block := "NodeBlock" }

/-- `LeafBlock1`'s carry: `%8 < 58` holds. -/
abbrev Scc₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₂ C with block := "LeafBlock1" }

/-- `sw.default.i`'s carry: `%8 = 44` does not hold. -/
abbrev Scc₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₃ C with block := "sw.default.i" }

/-- `cond.true345.i`'s carry: the entry count's test succeeds at a continuing entry. -/
abbrev Scc₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₄ C with block := "cond.true345.i" }

/-- `cond.end349.i`'s carry: the bound is the next entry's position. -/
abbrev Scc₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₅ C with block := "cond.end349.i" }

/-- The whitespace check's carry: the bound is above the entry's index. -/
abbrev Scc₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₆ C with block := "land.lhs.true357.i" }

/-- The byte's first pivot's carry. -/
abbrev Scc₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₇ C with block := "NodeBlock41" }

/-- The byte's second pivot's carry. -/
abbrev Scc₉ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₈ C with block := "NodeBlock39" }

/-- `LeafBlock37`'s carry: the byte is not below `32` either, the no-run class. -/
abbrev Scc₁₀ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₉ C with block := "LeafBlock37" }

/-- The token's end's carry: the byte is not `32`, so no whitespace run. -/
abbrev Scc₁₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₁₀ C with block := "if.end372.i" }

/-- The tail's start carry: the tag test's true arm, the scalar kind. -/
abbrev Scc₁₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { Scc₁₁ C with block := "if.then413.i" }

/-! ### The states, named -/

/-- `NodeBlock21`'s target: `%Pivot22`'s bite on the arm to `NodeBlock5`. -/
def scS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock5", pre := some s.pc }

/-- `NodeBlock5`'s target: `%Pivot6`'s bite on the arm to `NodeBlock`. -/
def scS₂ (s : State) (x : BitVec 8) : State :=
  { (scS₁ s x).bind "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
    pc := "NodeBlock", pre := some (scS₁ s x).pc }

/-- `NodeBlock`'s target: `%Pivot`'s bite on the arm to `LeafBlock1`. -/
def scS₃ (s : State) (x : BitVec 8) : State :=
  { (scS₂ s x).bind "%Pivot" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 58))) with
    pc := "LeafBlock1", pre := some (scS₂ s x).pc }

/-- `LeafBlock1`'s target: `%SwitchLeaf2`'s bite on the arm to `sw.default.i`. -/
def scS₄ (s : State) (x : BitVec 8) : State :=
  { (scS₃ s x).bind "%SwitchLeaf2" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 44))) with
    pc := "sw.default.i", pre := some (scS₃ s x).pc }

/-- `sw.default.i`'s target on the count test's succeeding arm: `%cmp343.i`'s cell, at
`cond.true345.i`. -/
def scS₅ (s : State) (x : BitVec 8) (inc nep : BitVec 64) : State :=
  { (scS₄ s x).bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep)) with
    pc := "cond.true345.i", pre := some (scS₄ s x).pc }

/-- `cond.end349.i`'s target on the continuing arm: the bound's `phi` selects
`%conv347.i`, so `%cond350.i` is `ofNat 64 v.toNat`. -/
def sEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) : State :=
  condEnd349OutAt (cte345OutAt (scS₅ s x inc nep) ep inc v)
    (BitVec.ofNat 64 v.toNat) ix C.stage.tok (C.stage.tok + 20)

/-- **The scalar route's `cond.end349.i` target has the high-byte route's memory.**  The
lane load and the zero-extension write nothing and the two token-record stores are at the
same addresses, so the document's byte before the entry's end is the shared read. -/
theorem sEnd_mem {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) :
    (sEnd C s x inc nep ep v ix).mem = (contEndS C s x inc nep ep v ix).mem := rfl

/-- `land.lhs.true357.i`'s target: the byte before the entry's end and its address. -/
def sLand {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { (stateAt (cells [("%35", .int 8 (cont35 b35)), ("%gep", .ptr ((G.b - 1) + v.toNat))]
      (sEnd C s x inc nep ep v ix).env) (sEnd C s x inc nep ep v ix)) with
    pc := "NodeBlock41", pre := some (sEnd C s x inc nep ep v ix).pc }

/-- `NodeBlock41`'s target: `%35 < 13` does not hold. -/
def sP41 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((sLand C s x inc nep ep v ix b35).bind "%Pivot42"
      (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some (sLand C s x inc nep ep v ix b35).pc }

/-- `NodeBlock39`'s target: `%35 < 32` does not hold, the no-run class. -/
def sP39 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((sP41 C s x inc nep ep v ix b35).bind "%Pivot40"
      (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock37", pre := some (sP41 C s x inc nep ep v ix b35).pc }

/-- `LeafBlock37`'s target: `%35 = 37`'s equality test fails, so no whitespace run. -/
def sP35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((sP39 C s x inc nep ep v ix b35).bind "%SwitchLeaf38"
      (.int 1 (evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "if.end372.i", pre := some (sP39 C s x inc nep ep v ix b35).pc }

/-- **The tag-true seam**: `if.end372.i` with its successor named at the value call's
block.  `seamFin` carries the phi, the end store and the four comparison cells; only the
edge names the successor. -/
def scSeamS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { seamFin (sP35 C s x inc nep ep v ix b35) (BitVec.ofNat 64 v.toNat) x C.stage.tok with
    pc := "if.then413.i", pre := some (sP35 C s x inc nep ep v ix b35).pc }

/-- The scan-free tail's end: the copy call's test is `ult v v`, so the merge's entry is
reached without a scan. -/
def scEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) : State :=
  ScanEntry (scSeamS C s x inc nep ep v ix b35) r₁ r₂ r₃ v.toNat v.toNat cA rdv xA

/-- The tail's carry: the three calls' `TailCarryEnd`, from the tag-true seam's carry. -/
abbrev scTailC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  TailCarryEnd (HeadC₄₁₃ (ContAC₇ C)) ev

/-- The merge's carry: one block update on the tail's. -/
abbrev scMergeC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { scTailC C ev with block := "cleanup478.i" }

/-- The merge, named. -/
def scMergeS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) : State :=
  { scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA with
    pc := "cleanup478.i", pre := some "if.end473.i" }

/-! ### The scalar route's seam, at the byte's own route

`scSeamS` is the scalar route's seam at the **high leaf** (`LeafBlock37`, its equality test
clearing), and it is what `HcontScalarFacts`' three bits name.  The scalar route reaches
`if.then413.i` from the other two non-whitespace leaves as well — the pivots differ, the
seam's stored end, the `%8` test and the memory do not — so the seam is stated here at the
byte's own class, exactly as the continuing side's `contSeamByte` and the last entry's
`hlastSeamByte` are.  The high-leaf instance is `scSeamS` by `rfl`, which is what lets the
bundle's existing proofs keep reading it.

These are stated in this module because the scalar bundle's states live here; the bundle
itself is still the three-bit one, and the route-carrying restatement reads these. -/

/-- `NodeBlock41`'s target: the byte's first pivot, at `NodeBlock39`. -/
def sP41Out (q4 : State) (b35 : UInt8) : State :=
  { (q4.bind "%Pivot42" (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some q4.pc }

/-- `NodeBlock41`'s target on the arm its `%35 < 13` test takes: `LeafBlock33`. -/
def sP41Low (q4 : State) (b35 : UInt8) : State :=
  { (q4.bind "%Pivot42" (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "LeafBlock33", pre := some q4.pc }

/-- `LeafBlock33`'s target on the arm its offset test does not take: `if.end372.i`. -/
def sP33Out (q4 : State) (b35 : UInt8) : State :=
  { stateAt (cells
      [("%SwitchLeaf34", .int 1 (evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247)
        (BitVec.ofNat 8 1))),
       ("%.off", .int 8 (cont35 b35 + BitVec.ofNat 8 247))] q4.env) q4 with
    pc := "if.end372.i", pre := some q4.pc }

/-- `NodeBlock39`'s target: the byte's second pivot, at `LeafBlock35`. -/
def sP39Out (q4 : State) (b35 : UInt8) : State :=
  { (q4.bind "%Pivot40" (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock35", pre := some q4.pc }

/-- `NodeBlock39`'s target on the arm its `%35 < 32` test does not take: `LeafBlock37`. -/
def sP39High (q4 : State) (b35 : UInt8) : State :=
  { (q4.bind "%Pivot40" (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock37", pre := some q4.pc }

/-- `LeafBlock35`'s target on the arm its equality test does not take: `if.end372.i`. -/
def sP35Out (q4 : State) (b35 : UInt8) : State :=
  { (q4.bind "%SwitchLeaf36" (.int 1 (evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "if.end372.i", pre := some q4.pc }

/-- `LeafBlock37`'s target on the arm its equality test does not take: `if.end372.i`. -/
def sP37Out (q4 : State) (b35 : UInt8) : State :=
  { (q4.bind "%SwitchLeaf38" (.int 1 (evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "if.end372.i", pre := some q4.pc }

/-- The scan-free route's pivot endpoint, at any state at `NodeBlock41`. -/
def sP35Any (q4 : State) (b35 : UInt8) : State :=
  sP35Out (sP39Out (sP41Out q4 b35) b35) b35

/-- The low leaf's pivot endpoint, at any state at `NodeBlock41`. -/
def sP33Any (q4 : State) (b35 : UInt8) : State :=
  sP33Out (sP41Low q4 b35) b35

/-- The high leaf's pivot endpoint, at any state at `NodeBlock41`. -/
def sP37Any (q4 : State) (b35 : UInt8) : State :=
  sP37Out (sP39High (sP41Out q4 b35) b35) b35

/-- **The scalar route's seam, at the byte's own class**: `if.end372.i` with its
successor named at the value call's block, the tag test's true arm. -/
def scSeamByte (q4 : State) (vN : Nat) (x : BitVec 8) (tok : Nat) (b35 : UInt8)
    (hb : HcontByteRoute (cont35 b35)) : State :=
  match hb with
  | .scanFree _ _ _ =>
      { seamFin (sP35Any q4 b35) (BitVec.ofNat 64 vN) x tok with
        pc := "if.then413.i", pre := some (sP35Any q4 b35).pc }
  | .lowLeaf _ _ =>
      { seamFin (sP33Any q4 b35) (BitVec.ofNat 64 vN) x tok with
        pc := "if.then413.i", pre := some (sP33Any q4 b35).pc }
  | .highLeaf _ _ _ =>
      { seamFin (sP37Any q4 b35) (BitVec.ofNat 64 vN) x tok with
        pc := "if.then413.i", pre := some (sP37Any q4 b35).pc }

/-- **The high-leaf instance is the scalar route's seam.**  `scSeamS` is `scSeamByte` at
`.highLeaf`, definitionally: the generic pivots are the same record updates on the same
base, so the bundle's existing proofs read the route's seam without restatement. -/
theorem scSeamByte_highLeaf {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (h13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 0) :
    scSeamByte (sLand C s x inc nep ep v ix b35) v.toNat x C.stage.tok b35
        (.highLeaf h13 h32 hne32) =
      scSeamS C s x inc nep ep v ix b35 := rfl

/-! ### The cells the route reads

Each is a peel: the block that bound the name is one of the route's own. -/

/-- `%35` at the byte's first pivot. -/
theorem sLand_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sLand C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [sLand, stateAt, cells]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's second pivot. -/
theorem sP41_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sP41 C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [sP41, sLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's leaf. -/
theorem sP39_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sP39 C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [sP39, sP41, sLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the token's end's source. -/
theorem sP35_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sP35 C s x inc nep ep v ix b35).env "%SwitchLeaf38" =
      some (.int 1 (evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32))) := by
  simp only [sP35, stateAt, cells, State.bind]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the token's end: `cond.end349.i` bound it once. -/
theorem sP35_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sP35 C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [sP35, sP39, sP41, sLand, sEnd, condEnd349OutAt, cte345OutAt, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%8` at the token's end's source is the loop head's: the route binds `%35`, the
pivots' cells and the bound's cells, and none of them is the entry's byte. -/
theorem sP35_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sP35 C s x inc nep ep v ix b35).env "%8" = lookupName s.env "%8" := by
  simp only [sP35, sP39, sP41, sLand, sEnd, condEnd349OutAt, cte345OutAt, scS₅, scS₄,
    scS₃, scS₂, scS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the token's end's source is the loop head's. -/
theorem sP35_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sP35 C s x inc nep ep v ix b35).env "%end.i" = lookupName s.env "%end.i" := by
  simp only [sP35, sP39, sP41, sLand, sEnd, condEnd349OutAt, cte345OutAt, scS₅, scS₄,
    scS₃, scS₂, scS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The token's end's `phi` selects `%cond350.i` when the whitespace check is what sent
the walk there. -/
theorem scPhiSeam :
    phiIncoming "LeafBlock37"
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some (.reg "%cond350.i") := by
  decide

/-- `%ee.1.i` at the tail's start is the seam's stored end: `seamFin` binds it. -/
theorem scSeam_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (scSeamS C s x inc nep ep v ix b35).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [scSeamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the tail's start is the token's end. -/
theorem scSeam_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (scSeamS C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [scSeamS, seamFin, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact sP35_cond C s x inc nep ep v ix b35

/-- `%t352.i` at the tail's start is the token record's: the seam binds five cells and
none of them is it. -/
theorem scSeam_tok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (scSeamS C s x inc nep ep v ix b35).env "%t352.i" =
      lookupName (sP35 C s x inc nep ep v ix b35).env "%t352.i" := by
  simp only [scSeamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the tail's start is the head state's byte. -/
theorem scSeam_8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (scSeamS C s x inc nep ep v ix b35).env "%8" = lookupName s.env "%8" := by
  simp only [scSeamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact sP35_env8 C s x inc nep ep v ix b35

/-- `%inc.i` at the tail's end is the loop head's: the seam, the tail's three calls bind
their own cells and none is the header's increment. -/
theorem scEnd_inc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    lookupName (scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA).env "%inc.i" =
      lookupName s.env "%inc.i" := by
  simp only [scEnd, ScanEntry, TailS₃, TailS₂, TailS₁, scSeamS, seamFin, sP35, sP39, sP41,
    sLand, sEnd, condEnd349OutAt, cte345OutAt, scS₅, scS₄, scS₃, scS₂, scS₁, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the tail's end is the loop head's. -/
theorem scEnd_nep {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    lookupName (scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA).env "%nep" =
      lookupName s.env "%nep" := by
  simp only [scEnd, ScanEntry, TailS₃, TailS₂, TailS₁, scSeamS, seamFin, sP35, sP39, sP41,
    sLand, sEnd, condEnd349OutAt, cte345OutAt, scS₅, scS₄, scS₃, scS₂, scS₁, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%t352.i` at the tail's end is the token record's. -/
theorem scEnd_tok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    lookupName (scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA).env "%t352.i" =
      lookupName (sP35 C s x inc nep ep v ix b35).env "%t352.i" := by
  simp only [scEnd, ScanEntry, TailS₃, TailS₂, TailS₁, scSeamS, seamFin, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The scan-free tail's end is `if.end473.i`: the copy's test is `ult v v`. -/
theorem scEnd_pc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    (scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA).pc = "if.end473.i" := by
  show (if evalICmp .ult (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 v.toNat) = 1 then
    "land.rhs457.i" else "if.end473.i") = "if.end473.i"
  rw [hlast_ult_self (BitVec.ofNat 64 v.toNat)]
  rfl

/-- The merge's carry keeps the head state's index. -/
theorem scMergeC_k {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeC C ev).k = C.k := rfl

/-! ### The bundle -/

/-- **The scalar continuing token's facts.**  The head switch's *plain-value* arm: the
head byte's four pivots take `NodeBlock5 → NodeBlock → LeafBlock1`, the default arm's
count test succeeds at a continuing entry, the byte before the entry's end is the no-run
class, and the token's end's tag test is *true*.  This is the class the document `"01"`'s
byte `0x30` takes, and the one no arm of the old `HcontCase` covered.

Called *the scalar arm* rather than *the scan-free arm*, which is `HcontCleanupFacts`'s
name: that bundle is the same token-end shape on the high-byte route, and the difference is
the head byte's own dispatch.  The bundle carries the route's premises and the tail's three
calls; the segment and the price are `walkRevolutionMergeSegScalar`'s. -/
structure HcontScalarFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The head's byte and its four scalar-arm pivot bits, the same ones the last entry's
  plain-value arm states (`HeadArm.defaultValue`). -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1
  h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0
  h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1
  hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0
  /-- **The tag test is `1`**: a digit or `-`, so `if.end372.i` leaves for `if.then413.i`
  directly, with kind `7`.  This is the bit the high-byte route's class clears. -/
  hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
  /-- The counts and the count test's value: `1`, a continuing entry has one after it. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- The next entry's position lane: the table's pointer, the load's word and the read. -/
  ep : Nat
  v : BitVec 32
  h5 : lookupName (scS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (scS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The default arm's remaining cells. -/
  ix : BitVec 64
  hidx5 : lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  /-- The entry is not empty, so the whitespace check reads the byte before its end. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The byte before the entry's end and its no-run class**: `13 ≤ %35`, `32 ≤ %35`
  and `%35 ≠ 32` in the signed order, so the check takes `LeafBlock37`'s else arm and the
  token ends at the entry's end. -/
  b35 : UInt8
  hread35 : readBytes (sEnd C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0
  hbne32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 0
  /-- The tail's three calls and its event, on the empty arm, from the tag-true seam. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
    (scSeamS C s x inc nep ep v ix b35)
    (scTailC C ev)
    (scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA) 3

/-- The merge's endpoint, at the bundle's own terms. -/
abbrev scMergeF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontScalarFacts G C s) : State :=
  scMergeS C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA

/-- The tail's source, at the bundle's own terms. -/
abbrev scSeamF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontScalarFacts G C s) : State :=
  scSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35

/-- The tail's end, at the bundle's own terms. -/
abbrev scEndF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontScalarFacts G C s) : State :=
  scEnd C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA

/-! ### The head prefix: eight links

The scalar arm's four pivots, the count test's succeeding arm, `cond.true345.i`, the
bound's `phi` and the whitespace check.  It is `contPrefixLand`'s shape on this arm's
class, and it ends at the same block (`NodeBlock41`), which is why the three bytes' pivots
below append to either. -/
theorem scPrefixLand {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32}
    (hinc : evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    (h5 : lookupName (scS₅ s x inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (scS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx5 : lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (sEnd C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
      some [b35]) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₈ C)
      (sLand C s x inc nep ep v ix b35) 8 := by
  -- the arms, resolved by the class's bits
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [hlt91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "NodeBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 58) = 1 then
      "LeafBlock1" else "LeafBlock3") = "LeafBlock1" := by rw [h58]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 44) = 1 then
      "if.then127.i" else "sw.default.i") = "sw.default.i" := by rw [hne44]; rfl
  have hres₅ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.true345.i" := by rw [hnext]; rfl
  -- the byte's operand fact at each pivot
  have h8₁ : evalOperand (scS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₂ : evalOperand (scS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scS₂, scS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₃ : evalOperand (scS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scS₃, scS₂, scS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₄ : evalOperand (scS₄ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scS₄, scS₃, scS₂, scS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf2") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (Scc₁ C) (scS₁ s x) := by
    have hst : s₁ = scS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. the second pivot
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (Scc₁ C)
      (scS₁ s x) hl₁'.inv' rfl h8₁
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (Scc₁ C) (scS₁ s x)
      (Scc₂ C) (scS₂ s x) := by
    have hst : s₂ = scS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the third pivot
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock_at (calls := stage2Calls stage2SubCalls) G (Scc₂ C)
      (scS₂ s x) hl₂'.inv' rfl h8₂
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (Scc₂ C) (scS₂ s x)
      (Scc₃ C) (scS₃ s x) := by
    have hst : s₃ = scS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock1_at (calls := stage2Calls stage2SubCalls) G (Scc₃ C)
      (scS₃ s x) hl₃'.inv' rfl h8₃
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (Scc₃ C) (scS₃ s x)
      (Scc₄ C) (scS₄ s x) := by
    have hst : s₄ = scS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- 5. the default arm's entry count, on the succeeding arm
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (Scc₄ C)
      (scS₄ s x) hl₄'.inv' rfl hinc hnep
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (Scc₄ C) (scS₄ s x)
      (Scc₅ C) (scS₅ s x inc nep) := by
    have hst : s₅ = scS₅ s x inc nep := by rw [hs₅, hres₅]; rfl
    rw [hst] at hl₅
    rw [hres₅] at hl₅
    exact hl₅
  -- 6. the next entry's position lane
  have hincL : lookupName (scS₄ s x).env "%inc.i" = some (.int 64 inc) := by
    simpa only [evalOperand] using hinc
  have hinc5 : lookupName (scS₅ s x inc nep).env "%inc.i" = some (.int 64 inc) := by
    simp only [scS₅, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%inc.i") _ _ (by decide)]
    exact hincL
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.cond_true345_i_at (calls := stage2Calls stage2SubCalls) G (Scc₅ C)
      (scS₅ s x inc nep) hl₅'.inv' rfl h5 hinc5 hi63 hread
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (Scc₅ C) (scS₅ s x inc nep)
      (Scc₆ C) (cte345OutAt (scS₅ s x inc nep) ep inc v) := by
    rw [hs₆] at hl₆
    exact hl₆
  -- 7. the bound's `phi` and the position's compare, on the non-empty arm
  have hidx6 : lookupName (cte345OutAt (scS₅ s x inc nep) ep inc v).env "%idxprom.i" =
      some (.int 64 ix) := by
    rw [cte345OutAt_envIdx]; exact hidx5
  have htok6 : lookupName (cte345OutAt (scS₅ s x inc nep) ep inc v).env "%t352.i" =
      some (.ptr C.stage.tok) := by
    rw [cte345OutAt_envTok]; exact htok5
  have hgap6 : lookupName (cte345OutAt (scS₅ s x inc nep) ep inc v).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)) := by
    rw [cte345OutAt_envGap]; exact hgap5
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.cond_end349_i_at G (Scc₆ C)
      (cte345OutAt (scS₅ s x inc nep) ep inc v) hl₆'.inv' rfl
      (p := "cond.true345.i") rfl contPhi6
      (cte345OutAt_conv (scS₅ s x inc nep) ep inc v) hidx6 htok6 hgap6
  have hres₇ : (if evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G (Scc₆ C)
      (cte345OutAt (scS₅ s x inc nep) ep inc v) (Scc₇ C)
      (sEnd C s x inc nep ep v ix) := by
    have hst : s₇ = sEnd C s x inc nep ep v ix := by rw [hs₇]; rfl
    rw [hst] at hl₇
    rw [hres₇] at hl₇
    exact hl₇
  -- 8. the byte before the entry's end
  have hig : lookupName (sEnd C s x inc nep ep v ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    hl₇'.inv'.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (sEnd C s x inc nep ep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    simp only [sEnd, condEnd349OutAt, cells]
    rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hq63 : v.toNat < 2 ^ 63 := by have := v.isLt; omega
  obtain ⟨s₈, hl₈, hs₈⟩ :=
    WalkLink.land_lhs_true357_i_at G (Scc₇ C) (sEnd C s x inc nep ep v ix)
      hl₇'.inv' rfl (ig := G.b - 1) (q := v.toNat) (b := b35) hig hcond hq63 hread35
  have hl₈' : WalkLink (stage2Calls stage2SubCalls) G (Scc₇ C)
      (sEnd C s x inc nep ep v ix) (Scc₈ C)
      (sLand C s x inc nep ep v ix b35) := by
    rw [hs₈] at hl₈
    exact hl₈
  exact (Seg.measure
    (Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
      (Seg.tail hl₅' (Seg.tail hl₆' (Seg.tail hl₇' (Seg.tail hl₈'
        (Seg.nil hl₈'.inv'))))))))))

/-! ### The byte's pivots and the token's end: three links -/

/-- **`NodeBlock41` to `if.end372.i`, counted at three**, on `LeafBlock37`'s else arm:
the byte's two pivots and its equality test, with no whitespace run. -/
theorem scWsLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (hInv : WalkInv G (Scc₈ C) (sLand C s x inc nep ep v ix b35))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 0) :
    Seg (stage2Calls stage2SubCalls) G (Scc₈ C) (sLand C s x inc nep ep v ix b35)
      (Scc₁₁ C) (sP35 C s x inc nep ep v ix b35) 3 := by
  -- the byte's first pivot
  have h35a : evalOperand (sLand C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact sLand_35 C s x inc nep ep v ix b35
  obtain ⟨s₉, hl₉, hs₉⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G (Scc₈ C)
      (sLand C s x inc nep ep v ix b35) hInv rfl h35a
  have hl₉' : WalkLink (stage2Calls stage2SubCalls) G (Scc₈ C)
      (sLand C s x inc nep ep v ix b35) (Scc₉ C)
      (sP41 C s x inc nep ep v ix b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₉ = sP41 C s x inc nep ep v ix b35 := by rw [hs₉, harm]; rfl
    rw [hst] at hl₉
    rw [harm] at hl₉
    exact hl₉
  -- the byte's second pivot
  have h35b : evalOperand (sP41 C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact sP41_35 C s x inc nep ep v ix b35
  obtain ⟨s₁₀, hl₁₀, hs₁₀⟩ :=
    WalkLink.NodeBlock39_at (calls := stage2Calls stage2SubCalls) G (Scc₉ C)
      (sP41 C s x inc nep ep v ix b35) hl₉'.inv' rfl h35b
  have hl₁₀' : WalkLink (stage2Calls stage2SubCalls) G (Scc₉ C)
      (sP41 C s x inc nep ep v ix b35) (Scc₁₀ C)
      (sP39 C s x inc nep ep v ix b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock37" := by rw [hb32]; rfl
    have hst : s₁₀ = sP39 C s x inc nep ep v ix b35 := by rw [hs₁₀, harm]; rfl
    rw [hst] at hl₁₀
    rw [harm] at hl₁₀
    exact hl₁₀
  -- the leaf's equality test
  have h35c : evalOperand (sP39 C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact sP39_35 C s x inc nep ep v ix b35
  obtain ⟨s₁₁, hl₁₁, hs₁₁⟩ :=
    WalkLink.LeafBlock37_at (calls := stage2Calls stage2SubCalls) G (Scc₁₀ C)
      (sP39 C s x inc nep ep v ix b35) hl₁₀'.inv' rfl h35c
  have hl₁₁' : WalkLink (stage2Calls stage2SubCalls) G (Scc₁₀ C)
      (sP39 C s x inc nep ep v ix b35) (Scc₁₁ C)
      (sP35 C s x inc nep ep v ix b35) := by
    have harm : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by rw [hbne32]; rfl
    have hst : s₁₁ = sP35 C s x inc nep ep v ix b35 := by rw [hs₁₁, harm]; rfl
    rw [hst] at hl₁₁
    rw [harm] at hl₁₁
    exact hl₁₁
  exact Seg.tail hl₉' (Seg.tail hl₁₀' (Seg.tail hl₁₁' (Seg.nil hl₁₁'.inv')))

/-! ### The tag-true seam: one link -/

/-- **The token's end leaves for the value call**, on its tag test's `1` arm.  The
successor is `seamFin`'s at `if.then413.i`, named so the tail appends there. -/
theorem scSeamSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (hInv : WalkInv G (Scc₁₁ C) (sP35 C s x inc nep ep v ix b35))
    (h8 : lookupName (sP35 C s x inc nep ep v ix b35).env "%8" = some (.int 8 x))
    (hend : lookupName (sP35 C s x inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    Seg (stage2Calls stage2SubCalls) G (Scc₁₁ C) (sP35 C s x inc nep ep v ix b35)
      (Scc₁₂ C) (scSeamS C s x inc nep ep v ix b35) 1 := by
  have hcond : evalOperand (sP35 C s x inc nep ep v ix b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    simp only [evalOperand]
    exact sP35_cond C s x inc nep ep v ix b35
  obtain ⟨s₁₂, hl₁₂, hs₁₂⟩ :=
    WalkLink.if_end372_i_true_at (calls := stage2Calls stage2SubCalls) (G := G)
      (C := Scc₁₁ C) (s := sP35 C s x inc nep ep v ix b35) hInv rfl
      (p := "LeafBlock37") rfl scPhiSeam hcond hend h8 hbit
  have hl₁₂' : WalkLink (stage2Calls stage2SubCalls) G (Scc₁₁ C)
      (sP35 C s x inc nep ep v ix b35) (Scc₁₂ C)
      (scSeamS C s x inc nep ep v ix b35) := by
    rw [hs₁₂] at hl₁₂
    exact hl₁₂
  exact Seg.tail hl₁₂' (Seg.nil hl₁₂'.inv')

/-! ### The composition, and the dispatch result -/

/-- **The scalar continuing entry's path to the merge, counted at sixteen.**  The head's
twelve links, the tail's three on its empty arm and the merge's step.  The price is
`18 ≤ 32·Δk` at `Δk = 1` with the entry's span as the byte credit it does not spend.

The three cells are the merge's own: `%inc.i` and `%nep` peeled through the seam, the
span and the tail's three calls, and the carry's index (`scMergeC_k`, `rfl`).  The count
guard `_hk` is taken for uniformity with the other arms but not read: this arm's price is
the entry allowance's alone, and no byte or count credit enters it. -/
theorem walkRevolutionMergeSegScalar {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (_hk : C.k + 1 < G.nep) (f : HcontScalarFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (scMergeC C f.ev) (scMergeF f) 16 ∧
      WalkInv G (scMergeC C f.ev) (scMergeF f) ∧
      (scMergeC C f.ev).block = "cleanup478.i" ∧
      (scMergeF f).pre = some "if.end473.i" ∧
      (scMergeC C f.ev).k = C.k ∧
      lookupName (scMergeF f).env "%inc.i" =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName (scMergeF f).env "%nep" =
        some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      18 ≤ stage2EntryAllowance * (C.k + 1 - C.k) := by
  -- 1. the head's eight links
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₈ C)
      (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 8 :=
    scPrefixLand (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.h44 f.h58 f.hne44
      f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt f.hread35
  -- 2. the byte's pivots and the token's end: three links
  have hseg3 : Seg (stage2Calls stage2SubCalls) G (Scc₈ C)
      (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (Scc₁₁ C)
      (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 3 :=
    scWsLeafSeg (G := G) (C := C) (s := s) f.x f.inc f.nep f.ep f.v f.ix f.b35 hseg8.inv'
      f.hb13 f.hb32 f.hbne32
  -- 3. the tag-true seam: one link
  have h8p : lookupName (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env "%8" =
      some (.int 8 f.x) := by
    rw [sP35_env8]; exact f.h8
  have hendp : lookupName (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) := by
    rw [sP35_envEnd]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have hseg1 : Seg (stage2Calls stage2SubCalls) G (Scc₁₁ C)
      (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (Scc₁₂ C)
      (scSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 1 :=
    scSeamSeg (G := G) (C := C) (s := s) f.x f.inc f.nep f.ep f.v f.ix f.b35
      (Seg.measure hseg3).inv' h8p hendp f.hbit
  -- 4. the tail's three links, on the empty arm
  have hsegP : WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₁₂ C)
      (scSeamF f) 12 :=
    hseg8.trans ((Seg.measure hseg3).trans (Seg.measure hseg1))
  have htail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamF f) (scTailC C f.ev) (scEndF f) 3 := f.hTail
  have hseg15 : WalkSegment (stage2Calls stage2SubCalls) G C s (scTailC C f.ev)
      (scEndF f) 15 := by
    -- the carry at the seam is `HeadC₄₁₃ (ContAC₇ C)`; the segment's target joins it
    have hcarry : Scc₁₂ C = HeadC₄₁₃ (ContAC₇ C) := rfl
    rw [hcarry] at hsegP
    exact hsegP.trans htail
  -- 5. the merge's empty step
  have htok : lookupName (scEndF f).env "%t352.i" = some (.ptr C.stage.tok) := by
    rw [scEnd_tok]
    exact f.htok5
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := scTailC C f.ev)
      (s := scEndF f) hseg15.inv' rfl htok
  have hpc : (scEndF f).pc = "if.end473.i" := scEnd_pc C s f.x f.inc f.nep f.ep f.v f.ix f.b35
    f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
  rw [hpc] at hs₂
  have hs₂' : s₂ = scMergeF f := hs₂
  subst hs₂'
  -- the cells at the merge
  have hincM : lookupName (scMergeF f).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [show (scMergeF f).env = (scEndF f).env from rfl, scEnd_inc]
    exact hInv.inc_reg
  have hnepM : lookupName (scMergeF f).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [show (scMergeF f).env = (scEndF f).env from rfl, scEnd_nep]
    exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  refine ⟨hseg15.trans (WalkSegment.of_link hl₂), hl₂.inv', rfl, rfl, scMergeC_k C f.ev,
    hincM, hnepM, ?_⟩
  have hΔ : C.k + 1 - C.k = 1 := by omega
  simp only [stage2EntryAllowance, hΔ, Nat.mul_one]
  decide

/-- **`WalkDispatch`'s body on the scalar arm.**  The composition's endpoint and its
three cells, in the dispatch's own shape: the index is `C.k + 1`, the depth is the
invariant's, and the price is the arm's own `p + 2 ≤ 32·Δk + 8·ΔA`. -/
theorem walkDispatch_at_continue_scalar {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (hcont : HcontScalarFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      Cd.k = C.k ∧
      sd.pre = some prev ∧
      phiIncoming prev cleanupSpIncoming = some spOp ∧
      evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)) ∧
      phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧
      k2 < nepv.toNat ∧
      k2 < G.nep ∧
      C.k < k2 ∧
      spv ≤ stage2StackExtent ∧
      spv ≤ Cd.wlen ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) := by
  obtain ⟨hseg, hInvD, hblockD, hpre, hkC, hinc, hnep, hprice⟩ :=
    walkRevolutionMergeSegScalar G C s hInv hhead hk hcont
  have hdepth : evalOperand (scMergeF hcont) (Operand.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 (scMergeC C hcont.ev).sp)) := hInvD.depth_reg
  have hincv : evalOperand (scMergeF hcont) (Operand.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := hinc
  have hnep64 : G.nep < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
  refine ⟨scMergeC C hcont.ev, scMergeF hcont, 16, (scMergeC C hcont.ev).sp,
    C.k + 1, "if.end473.i", Operand.reg "%sp.i.0248", Operand.reg "%inc.i",
    BitVec.ofNat 64 G.nep, hseg, hblockD, hkC, hpre, (by decide), hdepth, (by decide),
    hincv, hnep, ?_, hk, ?_, hInvD.depth_cap, hInvD.sp_le_wlen, ?_⟩
  · rw [hnepv]; exact hk
  · omega
  · have hΔ : C.k + 1 - C.k = 1 := by omega
    have h0 : 0 ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) := Nat.zero_le _
    simp only [stage2EntryAllowance, hΔ, Nat.mul_one] at hprice ⊢
    omega

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.sEnd_mem
#print axioms LeanLLVM.Refinement.WalkScope.scPrefixLand
#print axioms LeanLLVM.Refinement.WalkScope.scWsLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.scSeamSeg
#print axioms LeanLLVM.Refinement.WalkScope.scEnd_inc
#print axioms LeanLLVM.Refinement.WalkScope.scEnd_nep
#print axioms LeanLLVM.Refinement.WalkScope.scEnd_tok
#print axioms LeanLLVM.Refinement.WalkScope.scEnd_pc
#print axioms LeanLLVM.Refinement.WalkScope.walkRevolutionMergeSegScalar
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_continue_scalar

/-- `%35` survives `NodeBlock41`'s first pivot. -/
theorem sP41Out_35 (q4 : State) (b35 : UInt8) :
    lookupName (sP41Out q4 b35).env "%35" = lookupName q4.env "%35" := by
  simp only [sP41Out, State.bind]
  rw [lookupName_cons_ne (k := "%Pivot42") (n := "%35") _ _ (by decide)]

/-- `%35` survives `NodeBlock41`'s low arm. -/
theorem sP41Low_35 (q4 : State) (b35 : UInt8) :
    lookupName (sP41Low q4 b35).env "%35" = lookupName q4.env "%35" := by
  simp only [sP41Low, State.bind]
  rw [lookupName_cons_ne (k := "%Pivot42") (n := "%35") _ _ (by decide)]

/-- `%35` at `NodeBlock39`'s target is the `NodeBlock41` state's. -/
theorem sP39Out_35 (q4 : State) (b35 : UInt8) :
    lookupName (sP39Out q4 b35).env "%35" = lookupName q4.env "%35" := by
  simp only [sP39Out, State.bind]
  rw [lookupName_cons_ne (k := "%Pivot40") (n := "%35") _ _ (by decide)]

/-- `%35` survives `NodeBlock39`'s high arm. -/
theorem sP39High_35 (q4 : State) (b35 : UInt8) :
    lookupName (sP39High q4 b35).env "%35" = lookupName q4.env "%35" := by
  simp only [sP39High, State.bind]
  rw [lookupName_cons_ne (k := "%Pivot40") (n := "%35") _ _ (by decide)]

/-- `%cond350.i` at the scan-free endpoint is the `NodeBlock41` state's. -/
theorem sP35Any_cond (q4 : State) (b35 : UInt8) :
    lookupName (sP35Any q4 b35).env "%cond350.i" = lookupName q4.env "%cond350.i" := by
  simp only [sP35Any, sP35Out, sP39Out, sP41Out, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the scan-free endpoint is the `NodeBlock41` state's. -/
theorem sP35Any_envEnd (q4 : State) (b35 : UInt8) :
    lookupName (sP35Any q4 b35).env "%end.i" = lookupName q4.env "%end.i" := by
  simp only [sP35Any, sP35Out, sP39Out, sP41Out, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the scan-free endpoint is the `NodeBlock41` state's. -/
theorem sP35Any_env8 (q4 : State) (b35 : UInt8) :
    lookupName (sP35Any q4 b35).env "%8" = lookupName q4.env "%8" := by
  simp only [sP35Any, sP35Out, sP39Out, sP41Out, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the low leaf's endpoint is the `NodeBlock41` state's. -/
theorem sP33Any_cond (q4 : State) (b35 : UInt8) :
    lookupName (sP33Any q4 b35).env "%cond350.i" = lookupName q4.env "%cond350.i" := by
  simp only [sP33Any, sP33Out, sP41Low, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the low leaf's endpoint is the `NodeBlock41` state's. -/
theorem sP33Any_envEnd (q4 : State) (b35 : UInt8) :
    lookupName (sP33Any q4 b35).env "%end.i" = lookupName q4.env "%end.i" := by
  simp only [sP33Any, sP33Out, sP41Low, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the low leaf's endpoint is the `NodeBlock41` state's. -/
theorem sP33Any_env8 (q4 : State) (b35 : UInt8) :
    lookupName (sP33Any q4 b35).env "%8" = lookupName q4.env "%8" := by
  simp only [sP33Any, sP33Out, sP41Low, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the high leaf's endpoint is the `NodeBlock41` state's. -/
theorem sP37Any_cond (q4 : State) (b35 : UInt8) :
    lookupName (sP37Any q4 b35).env "%cond350.i" = lookupName q4.env "%cond350.i" := by
  simp only [sP37Any, sP37Out, sP39High, sP41Out, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the high leaf's endpoint is the `NodeBlock41` state's. -/
theorem sP37Any_envEnd (q4 : State) (b35 : UInt8) :
    lookupName (sP37Any q4 b35).env "%end.i" = lookupName q4.env "%end.i" := by
  simp only [sP37Any, sP37Out, sP39High, sP41Out, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the high leaf's endpoint is the `NodeBlock41` state's. -/
theorem sP37Any_env8 (q4 : State) (b35 : UInt8) :
    lookupName (sP37Any q4 b35).env "%8" = lookupName q4.env "%8" := by
  simp only [sP37Any, sP37Out, sP39High, sP41Out, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The scalar route's pivots and its seam link, at the byte's class

Three segments per class, stated once at any state at `NodeBlock41`: the pivots to
`if.end372.i` (three links on the scan-free and high leaves, two on the low leaf) and the
seam's own link at the tag test's true arm.  The high-leaf instances are `scWsLeafSeg` and
`scSeamSeg`, by `rfl`. -/

/-- **The scan-free route's pivots**, `NodeBlock41 → NodeBlock39 → LeafBlock35 →
if.end372.i`. -/
theorem sPivotSegScanFree {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (Ca : WalkCarry G) (q4 : State) (hInv : WalkInv G Ca q4)
    (hblock : Ca.block = "NodeBlock41")
    {b35 : UInt8}
    (h35 : evalOperand q4 (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0) :
    Seg calls G Ca q4 { Ca with block := "if.end372.i" } (sP35Any q4 b35) 3 := by
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G Ca q4 hInv hblock h35
  have hl₅' : WalkLink calls G Ca q4 { Ca with block := "NodeBlock39" }
      (sP41Out q4 b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₅ = sP41Out q4 b35 := by rw [hs₅, harm]; rfl
    rw [hst] at hl₅
    rw [harm] at hl₅
    exact hl₅
  have h35b : evalOperand (sP41Out q4 b35) (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    rw [sP41Out_35]
    simpa only [evalOperand] using h35
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.NodeBlock39_at (calls := calls) G { Ca with block := "NodeBlock39" }
      (sP41Out q4 b35) hl₅'.inv' rfl h35b
  have hl₆' : WalkLink calls G { Ca with block := "NodeBlock39" } (sP41Out q4 b35)
      { { Ca with block := "NodeBlock39" } with block := "LeafBlock35" }
      (sP39Out (sP41Out q4 b35) b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := by rw [hb32]; rfl
    have hst : s₆ = sP39Out (sP41Out q4 b35) b35 := by rw [hs₆, harm]; rfl
    rw [hst] at hl₆
    rw [harm] at hl₆
    exact hl₆
  have h35c : evalOperand (sP39Out (sP41Out q4 b35) b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [sP39Out, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot40") (n := "%35") _ _ (by decide)]
    rw [sP41Out_35]
    simpa only [evalOperand] using h35
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.LeafBlock35_at (calls := calls) G
      { { Ca with block := "NodeBlock39" } with block := "LeafBlock35" }
      (sP39Out (sP41Out q4 b35) b35) hl₆'.inv' rfl h35c
  have hl₇' : WalkLink calls G
      { { Ca with block := "NodeBlock39" } with block := "LeafBlock35" }
      (sP39Out (sP41Out q4 b35) b35)
      { { { Ca with block := "NodeBlock39" } with block := "LeafBlock35" } with
        block := "if.end372.i" }
      (sP35Any q4 b35) := by
    have harm : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by
      rw [hbne13]; rfl
    have hst : s₇ = sP35Any q4 b35 := by
      rw [hs₇, harm]; rfl
    rw [hst] at hl₇
    rw [harm] at hl₇
    exact hl₇
  exact Seg.tail hl₅' (Seg.tail hl₆' (Seg.tail hl₇' (Seg.nil hl₇'.inv')))

/-- **The low leaf's pivots**, `NodeBlock41 → LeafBlock33 → if.end372.i`. -/
theorem sPivotSegLow {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (Ca : WalkCarry G) (q4 : State) (hInv : WalkInv G Ca q4)
    (hblock : Ca.block = "NodeBlock41")
    {b35 : UInt8}
    (h35 : evalOperand q4 (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hbns : evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) :
    Seg calls G Ca q4 { Ca with block := "if.end372.i" } (sP33Any q4 b35) 2 := by
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G Ca q4 hInv hblock h35
  have hl₅' : WalkLink calls G Ca q4 { Ca with block := "LeafBlock33" }
      (sP41Low q4 b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "LeafBlock33" := by rw [hb13]; rfl
    have hst : s₅ = sP41Low q4 b35 := by rw [hs₅, harm]; rfl
    rw [hst] at hl₅
    rw [harm] at hl₅
    exact hl₅
  have h35l : lookupName (sP41Low q4 b35).env "%35" = some (.int 8 (cont35 b35)) := by
    rw [sP41Low_35]
    simpa only [evalOperand] using h35
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.LeafBlock33_at (calls := calls) G { Ca with block := "LeafBlock33" }
      (sP41Low q4 b35) hl₅'.inv' rfl h35l
  have hl₆' : WalkLink calls G { Ca with block := "LeafBlock33" } (sP41Low q4 b35)
      { { Ca with block := "LeafBlock33" } with block := "if.end372.i" }
      (sP33Any q4 b35) := by
    have harm : (if evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247)
        (BitVec.ofNat 8 1) = 1 then "land.rhs.i.preheader" else "if.end372.i") =
        "if.end372.i" := by rw [hbns]; rfl
    have hst : s₆ = sP33Any q4 b35 := by
      rw [hs₆, harm]; rfl
    rw [hst] at hl₆
    rw [harm] at hl₆
    exact hl₆
  exact Seg.tail hl₅' (Seg.tail hl₆' (Seg.nil hl₆'.inv'))

/-- **The high leaf's pivots**, `NodeBlock41 → NodeBlock39 → LeafBlock37 →
if.end372.i` — `scWsLeafSeg`'s three links, at any state at `NodeBlock41`. -/
theorem sPivotSegHigh {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (Ca : WalkCarry G) (q4 : State) (hInv : WalkInv G Ca q4)
    (hblock : Ca.block = "NodeBlock41")
    {b35 : UInt8}
    (h35 : evalOperand q4 (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 0) :
    Seg calls G Ca q4 { Ca with block := "if.end372.i" } (sP37Any q4 b35) 3 := by
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G Ca q4 hInv hblock h35
  have hl₅' : WalkLink calls G Ca q4 { Ca with block := "NodeBlock39" }
      (sP41Out q4 b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₅ = sP41Out q4 b35 := by rw [hs₅, harm]; rfl
    rw [hst] at hl₅
    rw [harm] at hl₅
    exact hl₅
  have h35b : evalOperand (sP41Out q4 b35) (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    rw [sP41Out_35]
    simpa only [evalOperand] using h35
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.NodeBlock39_at (calls := calls) G { Ca with block := "NodeBlock39" }
      (sP41Out q4 b35) hl₅'.inv' rfl h35b
  have hl₆' : WalkLink calls G { Ca with block := "NodeBlock39" } (sP41Out q4 b35)
      { { Ca with block := "NodeBlock39" } with block := "LeafBlock37" }
      (sP39High (sP41Out q4 b35) b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock37" := by rw [hb32]; rfl
    have hst : s₆ = sP39High (sP41Out q4 b35) b35 := by rw [hs₆, harm]; rfl
    rw [hst] at hl₆
    rw [harm] at hl₆
    exact hl₆
  have h35h : evalOperand (sP39High (sP41Out q4 b35) b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [sP39High, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot40") (n := "%35") _ _ (by decide)]
    rw [sP41Out_35]
    simpa only [evalOperand] using h35
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.LeafBlock37_at (calls := calls) G
      { { Ca with block := "NodeBlock39" } with block := "LeafBlock37" }
      (sP39High (sP41Out q4 b35) b35) hl₆'.inv' rfl h35h
  have hl₇' : WalkLink calls G
      { { Ca with block := "NodeBlock39" } with block := "LeafBlock37" }
      (sP39High (sP41Out q4 b35) b35)
      { { { Ca with block := "NodeBlock39" } with block := "LeafBlock37" } with
        block := "if.end372.i" }
      (sP37Any q4 b35) := by
    have harm : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by
      rw [hbne32]; rfl
    have hst : s₇ = sP37Any q4 b35 := by
      rw [hs₇, harm]; rfl
    rw [hst] at hl₇
    rw [harm] at hl₇
    exact hl₇
  exact Seg.tail hl₅' (Seg.tail hl₆' (Seg.tail hl₇' (Seg.nil hl₇'.inv')))

/-! ### The scalar route's seam link, at the byte's class

`if.end372.i`'s tag test is `1`, so the walk leaves for `if.then413.i`; the endpoint is
the class's, and so is the `phi`'s matching predecessor.  These are `scSeamSeg`'s link at
the other two leaves. -/

/-- **The scan-free class's seam link.** -/
theorem sSeamByteSegScanFree {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (Ca : WalkCarry G) (q4 : State) {b35 : UInt8} {vN : Nat} {x : BitVec 8}
    (hInv : WalkInv G Ca (sP35Any q4 b35))
    (hl_blk : Ca.block = "if.end372.i")
    (hcond : lookupName (sP35Any q4 b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 vN)))
    (hend : lookupName (sP35Any q4 b35).env "%end.i" = some (.ptr (Ca.stage.tok + 8)))
    (h8q : lookupName (sP35Any q4 b35).env "%8" = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0) :
    Seg calls G Ca (sP35Any q4 b35) { Ca with block := "if.then413.i" }
      (scSeamByte q4 vN x Ca.stage.tok b35 (.scanFree hb13 hb32 hbne13)) 1 := by
  have hcondv : evalOperand (sP35Any q4 b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 vN)) := by
    simp only [evalOperand]
    exact hcond
  obtain ⟨s', hl, hs'⟩ :=
    WalkLink.if_end372_i_true_at (calls := calls) (G := G) (C := Ca)
      (s := sP35Any q4 b35) hInv hl_blk (p := "LeafBlock35") rfl hlast_phiSeam hcondv hend
      h8q hbit
  rw [hs'] at hl
  exact Seg.tail hl (Seg.nil hl.inv')

/-- **The low leaf's seam link.** -/
theorem sSeamByteSegLow {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (Ca : WalkCarry G) (q4 : State) {b35 : UInt8} {vN : Nat} {x : BitVec 8}
    (hInv : WalkInv G Ca (sP33Any q4 b35))
    (hl_blk : Ca.block = "if.end372.i")
    (hcond : lookupName (sP33Any q4 b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 vN)))
    (hend : lookupName (sP33Any q4 b35).env "%end.i" = some (.ptr (Ca.stage.tok + 8)))
    (h8q : lookupName (sP33Any q4 b35).env "%8" = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hbns : evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) :
    Seg calls G Ca (sP33Any q4 b35) { Ca with block := "if.then413.i" }
      (scSeamByte q4 vN x Ca.stage.tok b35 (.lowLeaf hb13 hbns)) 1 := by
  have hcondv : evalOperand (sP33Any q4 b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 vN)) := by
    simp only [evalOperand]
    exact hcond
  obtain ⟨s', hl, hs'⟩ :=
    WalkLink.if_end372_i_true_at (calls := calls) (G := G) (C := Ca)
      (s := sP33Any q4 b35) hInv hl_blk (p := "LeafBlock33") rfl hlastPhiSeam33 hcondv hend
      h8q hbit
  rw [hs'] at hl
  exact Seg.tail hl (Seg.nil hl.inv')

/-- **The high leaf's seam link** — `scSeamSeg`'s link, at any state at `if.end372.i`. -/
theorem sSeamByteSegHigh {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (Ca : WalkCarry G) (q4 : State) {b35 : UInt8} {vN : Nat} {x : BitVec 8}
    (hInv : WalkInv G Ca (sP37Any q4 b35))
    (hl_blk : Ca.block = "if.end372.i")
    (hcond : lookupName (sP37Any q4 b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 vN)))
    (hend : lookupName (sP37Any q4 b35).env "%end.i" = some (.ptr (Ca.stage.tok + 8)))
    (h8q : lookupName (sP37Any q4 b35).env "%8" = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 0) :
    Seg calls G Ca (sP37Any q4 b35) { Ca with block := "if.then413.i" }
      (scSeamByte q4 vN x Ca.stage.tok b35 (.highLeaf hb13 hb32 hbne32)) 1 := by
  have hcondv : evalOperand (sP37Any q4 b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 vN)) := by
    simp only [evalOperand]
    exact hcond
  obtain ⟨s', hl, hs'⟩ :=
    WalkLink.if_end372_i_true_at (calls := calls) (G := G) (C := Ca)
      (s := sP37Any q4 b35) hInv hl_blk (p := "LeafBlock37") rfl hlastPhiSeam37 hcondv hend
      h8q hbit
  rw [hs'] at hl
  exact Seg.tail hl (Seg.nil hl.inv')

end WalkScope
end LeanLLVM.Refinement
