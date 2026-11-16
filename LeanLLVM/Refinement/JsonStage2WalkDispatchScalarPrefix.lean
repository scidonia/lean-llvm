/-
The last entry's plain-value path: the scalar arm of the terminal dispatch.

## The arm

The head's switch (`NodeBlock21` and the six pivots below it) sends an ordinary byte to
`sw.default.i`; the last entry's count test there fails, so the token's end is the
stream's end (`%4`) and the walk reads the document's last byte for the whitespace
check.  The byte in `%8` then decides the *literal's kind*: a digit or `-` leaves
`if.end372.i` on its `or.cond677` arm, straight to `if.then413.i`, with `%.sink372 = 7`
— the scalar kind.  From there the three calls (`s2_value_pos`, `od_scalar_value`,
`s2_after_value`) and the extra-token test are the scan-free tail of `PrefixCount`, and
the merge follows.

This is the class the last-entry bundle excluded.  `hlast_toMerge`'s prefix takes the
*other* switch arm (`sw.default.i` reached through `NodeBlock19 → NodeBlock17 →
LeafBlock15`, i.e. the bytes 126 and 127) and the class-C span that follows; a digit
goes through `NodeBlock5 → NodeBlock → LeafBlock1` and the tag test's true arm, and
`hlastTailSeg`'s sixteen links are not this path.  What the two paths share is
everything from `if.then413.i`: the tail's carries and states are stated at their entry
state, so `consumerTailSegEmptyAt` serves both — with a different kind operand.

## The count

| piece | links |
|---|---|
| the head: `NodeBlock21`, `NodeBlock5`, `NodeBlock`, `LeafBlock1` | 4 |
| `sw.default.i`'s count test and `cond.end349.i`'s bound | 2 |
| the whitespace check: `land.lhs.true357.i`, `NodeBlock41`, `NodeBlock39`, `LeafBlock37` | 4 |
| the token's end `if.end372.i`, on its tag test's *true* arm | 1 |

`4 + 2 + 4 + 1 = 11` links to `if.then413.i`; the scan-free tail's three and the
merge's step make `15`.  At the last entry `Δk = 1` and the byte term is zero
(`entryPos G G.nep = 0`), so the price `15 + 2 = 17` sits inside the entry allowance
`32` — and the merge's own test on its index is what decides the outcome.

## What is stated and what is not

The segment is stated at the named states (`scalarS₁` … `scalarSeam`), not at a chain:
a `WalkSegment` is what the dispatch's result prices.  The three cells the whitespace
check and the seam read (`%35`, `%8`, `%cond350.i`) have their peel lemmas here, and
the static registers are `WalkInv.regs` at each link's own source, so the arm's only
premises are the document's byte class, the last-entry guard's cells and the tail's
call preconditions.

The tag test's *true* arm has no `_at` lemma beside `if_end372_i_at`'s else arm, so
`WalkLink.if_end372_i_true_at` is stated here: the same six-instruction block at the
other bit, with the target named at `if.then413.i`.
-/
import LeanLLVM.Refinement.JsonStage2WalkPrefixCount

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The carries

One per link, on the previous link's carry: the state's block and the block the next
link starts at are the same name, which is what makes the `with`-nest stay writable. -/

/-- `NodeBlock5`'s carry: `%8 < 91` holds. -/
abbrev ScalarC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock5" }

/-- `NodeBlock`'s carry: `%8 < 44` does not hold. -/
abbrev ScalarC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₁ C with block := "NodeBlock" }

/-- `LeafBlock1`'s carry: `%8 < 58` holds. -/
abbrev ScalarC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₂ C with block := "LeafBlock1" }

/-- `sw.default.i`'s carry: `%8 = 44` does not hold. -/
abbrev ScalarC₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₃ C with block := "sw.default.i" }

/-- `cond.end349.i`'s carry: the entry count's test fails at the last entry. -/
abbrev ScalarC₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₄ C with block := "cond.end349.i" }

/-- The whitespace check's carry: the bound is above the entry's index. -/
abbrev ScalarC₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₅ C with block := "land.lhs.true357.i" }

/-- `NodeBlock41`'s carry: the byte before the end is not below 13. -/
abbrev ScalarC₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₆ C with block := "NodeBlock41" }

/-- `NodeBlock39`'s carry: the byte is not below 32 either. -/
abbrev ScalarC₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₇ C with block := "NodeBlock39" }

/-- `LeafBlock37`'s carry: the byte is not 32, so no whitespace run. -/
abbrev ScalarC₉ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₈ C with block := "LeafBlock37" }

/-- The token's end's carry: the walk reaches `if.end372.i` with no run. -/
abbrev ScalarC₁₀ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₉ C with block := "if.end372.i" }

/-- The tail's start carry: the tag test's true arm, the scalar kind. -/
abbrev ScalarC₁₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ScalarC₁₀ C with block := "if.then413.i" }

/-! ### The states

Each is a link's successor in the form the link's own `denoteCode` leaves it: the cell
the block bound at the head of the environment, and the edge's `pc` and `pre`. -/

/-- `NodeBlock21`'s target: `%Pivot22`'s bite on the arm to `NodeBlock5`. -/
def scalarS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock5", pre := some s.pc }

/-- `NodeBlock5`'s target: `%Pivot6`'s bite on the arm to `NodeBlock`. -/
def scalarS₂ (s : State) (x : BitVec 8) : State :=
  { (scalarS₁ s x).bind "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
    pc := "NodeBlock", pre := some (scalarS₁ s x).pc }

/-- `NodeBlock`'s target: `%Pivot`'s bite on the arm to `LeafBlock1`. -/
def scalarS₃ (s : State) (x : BitVec 8) : State :=
  { (scalarS₂ s x).bind "%Pivot" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 58))) with
    pc := "LeafBlock1", pre := some (scalarS₂ s x).pc }

/-- `LeafBlock1`'s target: `%SwitchLeaf2`'s bite on the arm to `sw.default.i`. -/
def scalarS₄ (s : State) (x : BitVec 8) : State :=
  { (scalarS₃ s x).bind "%SwitchLeaf2" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 44))) with
    pc := "sw.default.i", pre := some (scalarS₃ s x).pc }

/-- `sw.default.i`'s target: `%cmp343.i`'s bite on the arm the count test fails. -/
def scalarS₅ (s : State) (x : BitVec 8) (inc nep : BitVec 64) : State :=
  { (scalarS₄ s x).bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep)) with
    pc := "cond.end349.i", pre := some (scalarS₄ s x).pc }

/-- `cond.end349.i`'s target: the bound's `phi`, the token's two stores and the byte
test.  The `pc` is the test's own (`condEnd349OutAt`), so the named state is the
whitespace check's on the arm `ugt = 1`. -/
def scalarEndS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) : State :=
  condEnd349OutAt (scalarS₅ s x inc nep) (BitVec.ofNat 64 v) ix C.stage.tok
    (C.stage.tok + 20)

/-- `land.lhs.true357.i`'s target: the byte before the token's end and its address. -/
def scalarLand {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { stateAt (cells [("%35", .int 8 (head35 b35)), ("%gep", .ptr ((G.b - 1) + v))]
      (scalarEndS C s x inc nep v ix).env) (scalarEndS C s x inc nep v ix) with
    pc := "NodeBlock41", pre := some (scalarEndS C s x inc nep v ix).pc }

/-- `NodeBlock41`'s target, on the arm its `%35 < 13` test does not take. -/
def scalarP41 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { ((scalarLand C s x inc nep v ix b35).bind "%Pivot42"
      (.int 1 (evalICmp .slt (head35 b35) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some (scalarLand C s x inc nep v ix b35).pc }

/-- `NodeBlock39`'s target, on the arm its `%35 < 32` test does not take. -/
def scalarP39 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { ((scalarP41 C s x inc nep v ix b35).bind "%Pivot40"
      (.int 1 (evalICmp .slt (head35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock37", pre := some (scalarP41 C s x inc nep v ix b35).pc }

/-- `LeafBlock37`'s target: `%35 = 32` does not hold, so no run is entered and the walk
reaches the token's end. -/
def scalarP37 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { ((scalarP39 C s x inc nep v ix b35).bind "%SwitchLeaf38"
      (.int 1 (evalICmp .eq (head35 b35) (BitVec.ofNat 8 32)))) with
    pc := "if.end372.i", pre := some (scalarP39 C s x inc nep v ix b35).pc }

/-- **`if.end372.i`'s target on its tag test's true arm**: the seam's state at the
value-position call, with the scalar kind.  `seamFin`'s five cells and the end store are
the else arm's; the `pc` is the arm's. -/
def scalarSeam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { seamFin (scalarP37 C s x inc nep v ix b35) (BitVec.ofNat 64 v) x C.stage.tok with
    pc := "if.then413.i", pre := some (scalarP37 C s x inc nep v ix b35).pc }

/-! ### The cells the path reads

The invariant carries the static registers at every link's own source, so only the
three *carried* cells need a peel: `%35` at the byte's pivots, `%8` through the whole
route, and `%cond350.i` at the token's end. -/

/-- `%35` at the byte's first pivot. -/
theorem scalarLand_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarLand C s x inc nep v ix b35).env "%35" =
      some (.int 8 (head35 b35)) := by
  simp only [scalarLand, stateAt, cells]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's second pivot. -/
theorem scalarP41_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarP41 C s x inc nep v ix b35).env "%35" =
      some (.int 8 (head35 b35)) := by
  simp only [scalarP41, scalarLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's leaf. -/
theorem scalarP39_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarP39 C s x inc nep v ix b35).env "%35" =
      some (.int 8 (head35 b35)) := by
  simp only [scalarP39, scalarP41, scalarLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The bound at the token's end's source.  `cond.end349.i` bound it once and the
whitespace check's pivots bind their own cells. -/
theorem scalarEndS_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) :
    lookupName (scalarEndS C s x inc nep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [scalarEndS, condEnd349OutAt, cells]
  rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the token's end's source: the same cell, through the four pivots. -/
theorem scalarP37_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarP37 C s x inc nep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [scalarP37, scalarP39, scalarP41, scalarLand, scalarEndS, condEnd349OutAt,
    stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%8` at the token's end's source is the loop head's: every block on the route binds
its own cell, and none of them is the entry's byte. -/
theorem scalarP37_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarP37 C s x inc nep v ix b35).env "%8" = lookupName s.env "%8" := by
  simp only [scalarP37, scalarP39, scalarP41, scalarLand, scalarEndS, scalarS₅, scalarS₄,
    scalarS₃, scalarS₂, scalarS₁, condEnd349OutAt, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The token's end's `phi` selects `%cond350.i` when the whitespace check sent the walk
there: the seed's edge on the no-run class. -/
theorem scalar_phiSeam :
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

/-! ### The tag test's true arm

`if.end372.i`'s six instructions are the phi, the end store, the `%8 = 45` test, the
`%8 - 48` subtraction, its unsigned comparison and the `or`.  On the `1` arm the walk
leaves for `if.then413.i`: the scalar kind's edge.  The proof is `if_end372_i_at`'s at
the other bit, with the target named at the tail's start. -/
theorem WalkLink.if_end372_i_true_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end372.i")
    {p : String} {op : Operand} {e : BitVec 64} {b8 : BitVec 8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hend : lookupName s.env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8 : lookupName s.env "%8" = some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "if.then413.i" } s' ∧
      s' = { seamFin s e b8 C.stage.tok with pc := "if.then413.i", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_end372_i (calls := calls) G C s hInv hblock hpre hin hv
    hend h8
  rw [show ({ C with block := (if (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1 then
      "if.then413.i" else "if.else387.i") } : WalkCarry G) =
      { C with block := "if.then413.i" } from by
    rw [hbit]; rfl] at hl
  refine ⟨s', hl, ?_⟩
  let m' : Mem := writeBytes s.mem (C.stage.tok + 8) (natToBytes e.toNat 8)
  let sFin : State :=
    stateAt (("%or.cond677.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
            evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
        ("%or.cond524.i", .int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) ::
        ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
        ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) { s with mem := m' }
  have hspecs : walkIf_end372_i.instrs =
      ([{ dst := "%ee.1.i", ty := Ty.int 64,
          incoming := [("cond.end349.i", (Operand.reg "%idxprom.i")),
            ("while.body370.i", (Operand.reg "%cond350.i")),
            ("LeafBlock43", (Operand.reg "%ee.0.i238")),
            ("LeafBlock46", (Operand.reg "%ee.0.i238")),
            ("LeafBlock48", (Operand.reg "%ee.0.i238")),
            ("LeafBlock33", (Operand.reg "%cond350.i")),
            ("LeafBlock35", (Operand.reg "%cond350.i")),
            ("LeafBlock37", (Operand.reg "%cond350.i"))] }].map PhiSpec.instr) ++
        [Instr.store (Ty.int 64) (Operand.reg "%ee.1.i") (Operand.reg "%end.i"),
         Instr.icmp "%cmp376.i" IPred.eq 8 (Operand.reg "%8")
           (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
         Instr.binop "%37" BinOp.add 8 (Operand.reg "%8")
           (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
         Instr.icmp "%or.cond524.i" IPred.ult 8 (Operand.reg "%37")
           (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
         Instr.binop "%or.cond677.i" BinOp.or 1 (Operand.reg "%cmp376.i")
           (Operand.reg "%or.cond524.i")] := by
    simp [walkIf_end372_i, PhiSpec.instr]
  have hden : denoteCode calls walkIf_end372_i.instrs s = some sFin := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%ee.1.i", ty := Ty.int 64,
            incoming := [("cond.end349.i", (Operand.reg "%idxprom.i")),
          ("while.body370.i", (Operand.reg "%cond350.i")),
          ("LeafBlock43", (Operand.reg "%ee.0.i238")),
          ("LeafBlock46", (Operand.reg "%ee.0.i238")),
          ("LeafBlock48", (Operand.reg "%ee.0.i238")),
          ("LeafBlock33", (Operand.reg "%cond350.i")),
          ("LeafBlock35", (Operand.reg "%cond350.i")),
          ("LeafBlock37", (Operand.reg "%cond350.i"))] }])
      (vs := [("%ee.1.i", .int 64 e)])
      (rest := [Instr.store (Ty.int 64) (Operand.reg "%ee.1.i") (Operand.reg "%end.i"),
        Instr.icmp "%cmp376.i" IPred.eq 8 (Operand.reg "%8")
          (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
        Instr.binop "%37" BinOp.add 8 (Operand.reg "%8")
          (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
        Instr.icmp "%or.cond524.i" IPred.ult 8 (Operand.reg "%37")
          (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
        Instr.binop "%or.cond677.i" BinOp.or 1 (Operand.reg "%cmp376.i")
          (Operand.reg "%or.cond524.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%ee.1.i", .int 64 e)] =
      stateAt (("%ee.1.i", .int 64 e) :: s.env) s from rfl]
    rw [denoteCode_store64 (calls := calls)
      (env := ("%ee.1.i", .int 64 e) :: s.env) (s := s)
      (v := "%ee.1.i") (p := "%end.i") (x := e) (a := C.stage.tok + 8)
      (by exact walkLookup_cons_self "%ee.1.i" (.int 64 e) s.env) hend]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%cmp376.i") (a := "%8") 8
      (x := b8) (c := BitVec.ofNat 8 45)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact h8)]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%37") (a := "%8") (w := 8) (x := b8) (c := BitVec.ofNat 8 208)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact h8)]
    rw [walkDenoteCode_icmp_imm (calls := calls)
      (env := ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
        ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%or.cond524.i") (a := "%37") IPred.ult 8
      (x := b8 + BitVec.ofNat 8 208) (c := BitVec.ofNat 8 10)
      (by exact walkLookup_cons_self "%37" (.int 8 (b8 + BitVec.ofNat 8 208)) (("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) :: ("%ee.1.i", .int 64 e) :: s.env))]
    rw [denoteCode_or_reg_w (calls := calls)
      (env := ("%or.cond524.i", .int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) ::
        ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
        ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%or.cond677.i") (a := "%cmp376.i") (b := "%or.cond524.i") (w := 1)
      (x := evalICmp .eq b8 (BitVec.ofNat 8 45))
      (y := evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact walkLookup_cons_self "%cmp376.i" (.int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) (("%ee.1.i", .int 64 e) :: s.env))
      (by exact walkLookup_cons_self "%or.cond524.i" (.int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) (("%37", .int 8 (b8 + BitVec.ofNat 8 208)) :: ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) :: ("%ee.1.i", .int 64 e) :: s.env))]
    rfl
  have hfind : stage2Body.findBlock s.pc = some walkIf_end372_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_end372_i_find
  have hterm : walkIf_end372_i.term =
      Term.condbr (Operand.reg "%or.cond677.i") "if.then413.i" "if.else387.i" := rfl
  have hstep0 : LeanLLVM.step calls stage2Body s =
      .jump { sFin with
        pc := (if evalICmp .eq b8 (BitVec.ofNat 8 45) ||| evalICmp .ult
            (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) = 1 then
          "if.then413.i" else "if.else387.i"), pre := some s.pc } := by
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%or.cond677.i") (tl := "if.then413.i")
      (fl := "if.else387.i")
      (bit := evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by exact walkLookup_cons_self "%or.cond677.i" (.int 1 (evalICmp .eq b8
          (BitVec.ofNat 8 45) ||| evalICmp .ult (b8 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) (("%or.cond524.i", .int 1 (evalICmp .ult
            (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
          ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
          ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
          ("%ee.1.i", .int 64 e) :: s.env))]
    dsimp only [sFin, m', stateAt]
  have hstep : LeanLLVM.step calls stage2Body s =
      .jump { seamFin s e b8 C.stage.tok with pc := "if.then413.i", pre := some s.pc } := by
    rw [hstep0]
    rw [show (if (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1 then
      "if.then413.i" else "if.else387.i") = "if.then413.i" from by rw [hbit]; rfl]
    rfl
  exact Ctrl.jump.inj (hl.step.symm.trans hstep)

/-! ### The head route to the whitespace check

Six links: the four pivots on the byte, `sw.default.i`'s failing count test and
`cond.end349.i`'s bound.  The byte's route is the comma-and-numeral one — `91 ≤ …` is
false, `44 ≤ …` is true, `58 ≤ …` is true, `= 44` is false — which is where a digit or
`-` stands. -/
/-- **An entry's position is inside the document**, at a header index below the count. -/
theorem scalar_entryPos_lt {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    entryPos G k < G.n :=
  entryPos_lt G hk

/-- **`ugt` at two staged words is `1` when the right word is strictly below the
left.** -/
theorem scalar_ugt_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : b < a) :
    evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  have h' : (BitVec.ofNat 64 b).toNat < (BitVec.ofNat 64 a).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact h
  rw [show evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
      = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a)) from rfl,
    show BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = true from
      (BitVec.ult_iff_toNat_lt).2 h']
  rfl

theorem scalarHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hnot : ¬ (C.k + 1 < G.nep)) :
    Seg (stage2Calls stage2SubCalls) G C s (ScalarC₆ C)
      (scalarEndS C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
        (BitVec.ofNat 64 (entryPos G C.k))) 6 := by
  -- the last index: the head's own guard and the count's bound
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by rw [hblock])
  have hk : C.k + 1 = G.nep := by have := hInv.k_le; omega
  have hqn : entryPos G C.k < G.n := scalar_entryPos_lt G hklt
  have hv63 : G.n < 2 ^ 63 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hugt : evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 (entryPos G C.k)) = 1 :=
    scalar_ugt_of_lt (by omega) (by omega) hqn
  -- the four arms, resolved by the byte's bits
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "NodeBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 58) = 1 then
      "LeafBlock1" else "LeafBlock3") = "LeafBlock1" := by rw [h58]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 44) = 1 then
      "if.then127.i" else "sw.default.i") = "sw.default.i" := by rw [hne44]; rfl
  have hres₅ : (if evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 1
      then "cond.true345.i" else "cond.end349.i") = "cond.end349.i" := by
    have hge : evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 0 := by
      rw [hk, hlast_ult_self]
    rw [hge]; rfl
  have hres₆ : (if evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 (entryPos G C.k))
      = 1 then "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  -- the byte at each pivot
  have h8₁ : evalOperand (scalarS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scalarS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₂ : evalOperand (scalarS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scalarS₂, scalarS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₃ : evalOperand (scalarS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scalarS₃, scalarS₂, scalarS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₄ : evalOperand (scalarS₄ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [scalarS₄, scalarS₃, scalarS₂, scalarS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf2") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (ScalarC₁ C) (scalarS₁ s x) := by
    have hst : s₁ = scalarS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. the second pivot
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (ScalarC₁ C)
      (scalarS₁ s x) hl₁'.inv' rfl h8₁
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₁ C) (scalarS₁ s x)
      (ScalarC₂ C) (scalarS₂ s x) := by
    have hst : s₂ = scalarS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the third pivot
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock_at (calls := stage2Calls stage2SubCalls) G (ScalarC₂ C)
      (scalarS₂ s x) hl₂'.inv' rfl h8₂
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₂ C) (scalarS₂ s x)
      (ScalarC₃ C) (scalarS₃ s x) := by
    have hst : s₃ = scalarS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock1_at (calls := stage2Calls stage2SubCalls) G (ScalarC₃ C)
      (scalarS₃ s x) hl₃'.inv' rfl h8₃
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₃ C) (scalarS₃ s x)
      (ScalarC₄ C) (scalarS₄ s x) := by
    have hst : s₄ = scalarS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- 5. the default arm's entry count, at the last entry's own word
  have hinc₄ : evalOperand (scalarS₄ s x) (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [show (ScalarC₄ C).k = C.k from rfl]
    exact hl₄'.inv'.inc_reg
  have hnep₄ : evalOperand (scalarS₄ s x) (.reg "%nep") =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    simp only [evalOperand]
    exact hl₄'.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
      (by simp [walkStaticRegs])
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (ScalarC₄ C)
      (scalarS₄ s x) hl₄'.inv' rfl hinc₄ hnep₄
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₄ C) (scalarS₄ s x)
      (ScalarC₅ C) (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)) := by
    have hst : s₅ = scalarS₅ s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) := by
      rw [hs₅, hres₅]; rfl
    rw [hst] at hl₅
    rw [hres₅] at hl₅
    exact hl₅
  -- 6. the token's position against the bound, on the last entry's arm
  have hfour₅ : lookupName (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep)).env "%4" = some (.int 64 (BitVec.ofNat 64 G.n)) :=
    hl₅'.inv'.regs ("%4", .int 64 (BitVec.ofNat 64 G.n)) (by simp [walkStaticRegs])
  have hidx₅ : lookupName (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep)).env "%idxprom.i" =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := hl₅'.inv'.idx_reg
  have htok₅ : lookupName (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep)).env "%t352.i" = some (.ptr C.stage.tok) :=
    hl₅'.inv'.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgap₅ : lookupName (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep)).env "%gap.i" = some (.ptr (C.stage.tok + 20)) :=
    hl₅'.inv'.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.cond_end349_i_at G (ScalarC₅ C)
      (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)) hl₅'.inv' rfl
      (p := "sw.default.i") rfl hlast_pre5 hfour₅ hidx₅ htok₅ hgap₅
  rw [hres₆] at hl₆
  rw [hs₆] at hl₆
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₅ C)
      (scalarS₅ s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep))
      (ScalarC₆ C)
      (scalarEndS C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
        (BitVec.ofNat 64 (entryPos G C.k))) := hl₆
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃'
    (Seg.tail hl₄' (Seg.tail hl₅' (Seg.tail hl₆' (Seg.nil hl₆'.inv'))))))

/-! ### The whitespace check and the token's end

Four links from the bound to `if.end372.i`: the byte's load, its two pivots and the
leaf's equality test.  The byte is the document's last — the staging's, not the
caller's — and the class is the no-run one: `13 ≤ %35`, `32 ≤ %35`, `%35 ≠ 32`. -/
theorem scalarWsSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {x : BitVec 8} (inc nep : BitVec 64) {v : Nat} {ix : BitVec 64} {b35 : UInt8}
    (hInv : WalkInv G (ScalarC₆ C) (scalarEndS C s x inc nep v ix))
    (hv63 : v < 2 ^ 63)
    (hread35 : readBytes (scalarEndS C s x inc nep v ix).mem ((G.b - 1) + v) 1 =
      some [b35])
    (hb13 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (head35 b35) (BitVec.ofNat 8 32) = 0) :
    Seg (stage2Calls stage2SubCalls) G (ScalarC₆ C) (scalarEndS C s x inc nep v ix)
      (ScalarC₁₀ C) (scalarP37 C s x inc nep v ix b35) 4 := by
  -- the byte's load, at the address the staging fixes
  have hig : lookupName (scalarEndS C s x inc nep v ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    hInv.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (scalarEndS C s x inc nep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := scalarEndS_cond C s x inc nep v ix
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.land_lhs_true357_i_at G (ScalarC₆ C) (scalarEndS C s x inc nep v ix) hInv rfl
      (ig := G.b - 1) (q := v) (b := b35) hig hcond hv63 hread35
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₆ C)
      (scalarEndS C s x inc nep v ix) (ScalarC₇ C) (scalarLand C s x inc nep v ix b35) := by
    rw [hs₇] at hl₇
    exact hl₇
  -- the byte's first pivot
  have h35a : evalOperand (scalarLand C s x inc nep v ix b35) (.reg "%35") =
      some (.int 8 (head35 b35)) := by
    simp only [evalOperand]
    exact scalarLand_35 C s x inc nep v ix b35
  obtain ⟨s₈, hl₈, hs₈⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G (ScalarC₇ C)
      (scalarLand C s x inc nep v ix b35) hl₇'.inv' rfl h35a
  have hl₈' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₇ C)
      (scalarLand C s x inc nep v ix b35) (ScalarC₈ C)
      (scalarP41 C s x inc nep v ix b35) := by
    have harm : (if evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₈ = scalarP41 C s x inc nep v ix b35 := by rw [hs₈, harm]; rfl
    rw [hst] at hl₈
    rw [harm] at hl₈
    exact hl₈
  -- the byte's second pivot
  have h35b : evalOperand (scalarP41 C s x inc nep v ix b35) (.reg "%35") =
      some (.int 8 (head35 b35)) := by
    simp only [evalOperand]
    exact scalarP41_35 C s x inc nep v ix b35
  obtain ⟨s₉, hl₉, hs₉⟩ :=
    WalkLink.NodeBlock39_at (calls := stage2Calls stage2SubCalls) G (ScalarC₈ C)
      (scalarP41 C s x inc nep v ix b35) hl₈'.inv' rfl h35b
  have hl₉' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₈ C)
      (scalarP41 C s x inc nep v ix b35) (ScalarC₉ C)
      (scalarP39 C s x inc nep v ix b35) := by
    have harm : (if evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock37" := by rw [hb32]; rfl
    have hst : s₉ = scalarP39 C s x inc nep v ix b35 := by rw [hs₉, harm]; rfl
    rw [hst] at hl₉
    rw [harm] at hl₉
    exact hl₉
  -- the leaf's equality test
  have h35c : evalOperand (scalarP39 C s x inc nep v ix b35) (.reg "%35") =
      some (.int 8 (head35 b35)) := by
    simp only [evalOperand]
    exact scalarP39_35 C s x inc nep v ix b35
  obtain ⟨s₁₀, hl₁₀, hs₁₀⟩ :=
    WalkLink.LeafBlock37_at (calls := stage2Calls stage2SubCalls) G (ScalarC₉ C)
      (scalarP39 C s x inc nep v ix b35) hl₉'.inv' rfl h35c
  have hl₁₀' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₉ C)
      (scalarP39 C s x inc nep v ix b35) (ScalarC₁₀ C)
      (scalarP37 C s x inc nep v ix b35) := by
    have harm : (if evalICmp .eq (head35 b35) (BitVec.ofNat 8 32) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by rw [hbne32]; rfl
    have hst : s₁₀ = scalarP37 C s x inc nep v ix b35 := by rw [hs₁₀, harm]; rfl
    rw [hst] at hl₁₀
    rw [harm] at hl₁₀
    exact hl₁₀
  exact Seg.tail hl₇' (Seg.tail hl₈' (Seg.tail hl₉' (Seg.tail hl₁₀'
    (Seg.nil hl₁₀'.inv'))))

/-! ### The token's end to the tail's start

One link, on the tag test's true arm: the scalar kind's edge. -/
theorem scalarSeamSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {x : BitVec 8} (inc nep : BitVec 64) {v : Nat} {ix : BitVec 64} {b35 : UInt8}
    (hInv : WalkInv G (ScalarC₁₀ C) (scalarP37 C s x inc nep v ix b35))
    (h8 : lookupName (scalarP37 C s x inc nep v ix b35).env "%8" = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    Seg (stage2Calls stage2SubCalls) G (ScalarC₁₀ C) (scalarP37 C s x inc nep v ix b35)
      (ScalarC₁₁ C) (scalarSeam C s x inc nep v ix b35) 1 := by
  have hcond : evalOperand (scalarP37 C s x inc nep v ix b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 v)) := by
    simp only [evalOperand]
    exact scalarP37_cond C s x inc nep v ix b35
  have hend : lookupName (scalarP37 C s x inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) :=
    hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  obtain ⟨s₁₁, hl₁₁, hs₁₁⟩ :=
    WalkLink.if_end372_i_true_at (calls := stage2Calls stage2SubCalls) (G := G)
      (C := ScalarC₁₀ C) (s := scalarP37 C s x inc nep v ix b35) hInv rfl
      (p := "LeafBlock37") rfl scalar_phiSeam hcond hend h8 hbit
  have hl₁₁' : WalkLink (stage2Calls stage2SubCalls) G (ScalarC₁₀ C)
      (scalarP37 C s x inc nep v ix b35) (ScalarC₁₁ C)
      (scalarSeam C s x inc nep v ix b35) := by
    rw [hs₁₁] at hl₁₁
    exact hl₁₁
  exact Seg.tail hl₁₁' (Seg.nil hl₁₁'.inv')

/-! ### The prefix, counted at eleven -/

/-- **The last entry's plain-value prefix.**  Eleven links from the loop head to the
value-position call: the byte's four pivots, the count test's failing arm, the bound's
`phi`, the whitespace check's four and the tag test's true arm. -/
theorem scalarPrefixSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hnot : ¬ (C.k + 1 < G.nep))
    {b35 : UInt8}
    (hread35 : readBytes (scalarEndS C s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep) G.n (BitVec.ofNat 64 (entryPos G C.k))).mem
      ((G.b - 1) + G.n) 1 = some [b35])
    (hb13 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (head35 b35) (BitVec.ofNat 8 32) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (ScalarC₁₁ C)
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
        (BitVec.ofNat 64 (entryPos G C.k)) b35) 11 := by
  have hv63 : G.n < 2 ^ 63 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hA := scalarHeadSeg (G := G) (C := C) (s := s) hInv hblock h8 h91 h44 h58 hne44 hnot
  have hB := scalarWsSeg (G := G) (C := C) (s := s) (x := x)
    (inc := BitVec.ofNat 64 (C.k + 1)) (nep := BitVec.ofNat 64 G.nep) (v := G.n)
    (ix := BitVec.ofNat 64 (entryPos G C.k)) (b35 := b35) (Seg.measure hA).inv' hv63
    hread35 hb13 hb32 hbne32
  have h8p : lookupName (scalarP37 C s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep) G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).env "%8" =
      some (.int 8 x) := by
    rw [scalarP37_env8 C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
      (BitVec.ofNat 64 (entryPos G C.k)) b35]
    exact h8
  have hC := scalarSeamSeg (G := G) (C := C) (s := s) (x := x)
    (inc := BitVec.ofNat 64 (C.k + 1)) (nep := BitVec.ofNat 64 G.nep) (v := G.n)
    (ix := BitVec.ofNat 64 (entryPos G C.k)) (b35 := b35) (Seg.measure hB).inv' h8p hbit
  exact (Seg.measure hA).trans ((Seg.measure hB).trans (Seg.measure hC))

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scalarHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end372_i_true_at
#print axioms LeanLLVM.Refinement.WalkScope.scalarWsSeg
#print axioms LeanLLVM.Refinement.WalkScope.scalarSeamSeg
#print axioms LeanLLVM.Refinement.WalkScope.scalarPrefixSeg

end WalkScope
end LeanLLVM.Refinement
