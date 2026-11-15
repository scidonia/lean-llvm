/-
# The whitespace skip's run: a measured draft

Not imported by any target and not built by `lake build` — the Lean library globs
`LeanLLVM/`, and the executables use `srcDir` elsewhere.  This file is kept because it
elaborates against the committed tree and it is the starting point for `contWsRun`:
it holds the definition layer for the skip's three leaf classes and four of the six
visit segments, including the exit visit, which an earlier attempt did not reach.

It was written in a scratch directory; it is committed here so a crash cannot take it.
When the run lands in `JsonStage2WalkRevolution`, this file goes: it is an instrument,
not a proof, and a draft that outlives its landing is dead weight.
-/

import LeanLLVM.Refinement.JsonStage2WalkInduce
import LeanLLVM.Refinement.JsonStage2WalkRevolutionPrefix

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The skip's byte, and the states its visits leave -/

/-- The document's byte at `p`: the byte every visit of the whitespace skip loads. -/
def wsByte {m0 : Mem} (G : WalkGeom m0) (p : Nat) : UInt8 := G.bs.getD p 0

/-- The byte's register value, as `land.rhs.i` binds `%36`. -/
def wsX {m0 : Mem} (G : WalkGeom m0) (p : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (wsByte G p).toNat

/-- **The byte `scanB` reads is `wsByte`**, at an index the sign-extension leaves alone. -/
theorem scanB_ofNat {m0 : Mem} (G : WalkGeom m0) {p : Nat} (hp : p < 2 ^ 63) :
    scanB G (BitVec.ofNat 64 p) = wsByte G p := by
  simp only [scanB, wsByte, BitVec.signExtend_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The state `land.rhs.i`'s step leaves at index `p`: the byte's cell and its address. -/
def wsLandS {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) : State :=
  landRhsIOutAt G s (BitVec.ofNat 64 p) (wsByte G p)

/-- The state the skip's leaf leaves on its back edge — the latch's next state — at the
class the byte's first pivot selects.  The three arms are the three leaves. -/
def wsLeafS {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) : State :=
  if evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 1 then
    leafBlock43OutAt (nodeBlock52OutAt (wsLandS G s p) (wsX G p)) (wsX G p)
  else if evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 1 then
    scanLeafBlock46Out
      (scanNodeBlock50Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p)
  else
    scanLeafBlock48Out
      (scanNodeBlock48Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p)

/-- The state the skip leaves at `if.end372.i`: the leaf's cells, at the seam's block. -/
def wsStopS {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) : State :=
  { wsLeafS G s p with pc := "if.end372.i" }

/-! ### The three leaves' names for the leaf state -/

theorem wsLeafS_43 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 1) :
    wsLeafS G s p = leafBlock43OutAt (nodeBlock52OutAt (wsLandS G s p) (wsX G p)) (wsX G p) := by
  simp only [wsLeafS, h]
  simp

theorem wsLeafS_46 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 1) :
    wsLeafS G s p = scanLeafBlock46Out
      (scanNodeBlock50Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p) := by
  simp only [wsLeafS, h13, h32]
  rfl

theorem wsLeafS_48 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 0) :
    wsLeafS G s p = scanLeafBlock48Out
      (scanNodeBlock48Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p) := by
  simp only [wsLeafS, h13, h32]
  rfl

/-! ### The landing state's cells -/

/-- `wsLandS`'s environment, named: the byte's two cells, then the counter's. -/
theorem wsLandS_env {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    (wsLandS G s p).env =
      ("%36", .int 8 (BitVec.ofNat 8 (wsByte G p).toNat)) ::
      ("%arrayidx367.i", .ptr (G.b + ((BitVec.ofNat 64 p).signExtend 64).toNat)) ::
      ("%ee.0.i238", .int 64 (BitVec.ofNat 64 p)) :: s.env := by
  simp only [wsLandS, landRhsIOutAt, stateAt, State.bindAll, State.bind, cells]

theorem wsLandS_ee {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    lookupName (wsLandS G s p).env "%ee.0.i238" =
      some (.int 64 (BitVec.ofNat 64 p)) := by
  rw [wsLandS_env, lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem wsLandS_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) {v : Nat}
    (h : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v))) :
    lookupName (wsLandS G s p).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
  rw [wsLandS_env, lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### A continuing visit, at the states the skip's own `def`s name

The atomic unit of the run: the latch's step and the dispatch's three links, from the
latch at `p` to the latch at `p + 1`, at `LeafBlock43`'s class.  The byte is the
document's, so the visit's hypotheses about it are this lemma's class premises. -/

theorem wsContinue43 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1)
    (hws0 : evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) :
    WalkSegment calls G C l { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by show v - (p + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hlt13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 1 := by
    rw [hb]; exact hlt13
  have hws' : evalICmp .ule
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0 := by
    rw [hb]; exact hws0
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 3 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hi₁
    have hseg := Seg.measure (calls := calls) (walkWhiteScanVisitSeg3_43
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hseg₁.inv' rfl hpre hin hv hpos hqn' halen hevlen hlt13' hws' hsc)
    rw [hb] at hseg
    rw [wsLeafS_43 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1) hlt13]
    simpa only [wsLandS, wsX, scanCarryLatchOf] using hseg
  exact hseg₁.trans hseg₂

/-- **A continuing visit at `LeafBlock46`'s class**, five links: the latch's step and the
four of the second pivot's first arm. -/
theorem wsContinue46 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 32) = 1)
    (hne13 : evalICmp .eq (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0) :
    WalkSegment calls G C l { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 5 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by show v - (p + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hge13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hge13
  have hlt32' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 1 := by
    rw [hb]; exact hlt32
  have hne13' : evalICmp .eq
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hne13
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hi₁
    have hseg := Seg.measure (calls := calls) (walkWhiteScanVisitSeg4_46
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hseg₁.inv' rfl hpre hin hv hpos hqn' halen hevlen hge13' hlt32' hne13' hsc)
    rw [hb] at hseg
    rw [wsLeafS_46 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      hge13 hlt32]
    simpa only [wsLandS, wsX, scanCarryLatchOf, scanCarryLeafBlock46, scanCarryNodeBlock50] using hseg
  exact hseg₁.trans hseg₂

/-- **A continuing visit at `LeafBlock48`'s class**, five links, the second pivot's second
arm. -/
theorem wsContinue48 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq (wsX G (p + 1)) (BitVec.ofNat 8 32) = 0) :
    WalkSegment calls G C l { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 5 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by show v - (p + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hge13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hge13
  have hge32' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 0 := by
    rw [hb]; exact hge32
  have hne32' : evalICmp .eq
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 0 := by
    rw [hb]; exact hne32
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hi₁
    have hseg := Seg.measure (calls := calls) (walkWhiteScanVisitSeg4_48
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hseg₁.inv' rfl hpre hin hv hpos hqn' halen hevlen hge13' hge32' hne32' hsc)
    rw [hb] at hseg
    rw [wsLeafS_48 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      hge13 hge32]
    simpa only [wsLandS, wsX, scanCarryLatchOf, scanCarryLeafBlock48, scanCarryNodeBlock50] using hseg
  exact hseg₁.trans hseg₂

/-! ### The latch's step, as the facts its visit needs

`scanLatch_visit_at`'s target, pinned with the cells the dispatch's hypotheses read, so a
visit lemma states its four facts at the name rather than rebuilding them. -/

theorem wsLatchOut_facts {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (l : State) (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v) :
    WalkSegment calls G C l { C with block := "land.rhs.i" }
        (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") 1 ∧
      WalkInv G { C with block := "land.rhs.i" }
        (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") ∧
      lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
        "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
      lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) ∧
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
        some "while.body370.i" := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by
      have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
      show v - (p + 1) ≤ C.inner
      omega, hlt, hcw, hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  exact ⟨hseg₁, hseg₁.inv', hi₁, hc₁, hpre⟩

/-! ### The dispatch's three links, at the leaf's exit arm

The visit of `walkWhiteScanVisitSeg3_43` with the leaf's own test set: the byte is `9` or
`10`, so `LeafBlock43` leaves for `if.end372.i` instead of the latch.  The local fact the
leaf's link takes is the latch's either way, so the only differences from the back-edge
statement are the arm and the target's block. -/

theorem wsVisit43Exit {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    Seg calls G C s
      { { { C with block := "NodeBlock52" } with block := "LeafBlock43" } with
        block := "if.end372.i" }
      { leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat) with pc := "if.end372.i" } 3 := by
  have hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1
      = some [G.bs.getD (e.signExtend 64).toNat 0] :=
    walkDoc_byte G C s hInv halen hevlen hqn
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.land_rhs_i_at G C s hInv hblock hpre hin hv hpos hread
  have hstep₁ : s₁ = landRhsIOutAt G s e (scanB G e) := by
    rw [hs₁]
    rfl
  rw [hstep₁] at hl₁
  have h36₁ : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells]
    rw [lookupName_cons_self]
  have h1 : evalOperand (landRhsIOutAt G s e (scanB G e)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₁
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock52_at G { C with block := "NodeBlock52" } (landRhsIOutAt G s e (scanB G e))
      hl₁.inv' rfl h1
  have hstep₂ : s₂ = nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₂]
    simp only [nodeBlock52OutAt, if_pos hlt13]
  rw [hstep₂] at hl₂
  rw [show (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "LeafBlock43" from if_pos hlt13] at hl₂
  have h36₂ : lookupName (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hsc₃ : ScanCount
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc
      [("%SwitchLeaf45", .int 1 (evalICmp .ule
          (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
       ("%.off44", .int 8 (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247))]
      (by
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact ⟨by simp, by simp⟩)
  have hloc : WalkLocal { { C with block := "NodeBlock52" } with block := "while.body370.i" }
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) := by
    rw [WalkLocal.whitespace rfl]
    exact hsc₃
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock43_at G _
      (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      hl₂.inv' (by simp) h36₂ hloc
  have hres : (if evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 then "if.end372.i" else "while.body370.i") = "if.end372.i" :=
    if_pos hws
  have hstep₃ : s₃ = { leafBlock43OutAt
      (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      (BitVec.ofNat 8 (scanB G e).toNat) with pc := "if.end372.i" } := by
    rw [hs₃]
    simp only [leafBlock43OutAt, hres]
  rw [hstep₃] at hl₃
  rw [hres] at hl₃
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.nil hl₃.inv')))

