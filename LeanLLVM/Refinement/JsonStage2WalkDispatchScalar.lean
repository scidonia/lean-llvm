/-
The scalar arm: the plain-value path's tail and the dispatch's `merge` result.

`JsonStage2WalkDispatchScalarPrefix` proves the eleven links from the loop head to the
value-position call for a byte the switch sends to `sw.default.i` with the tag test's
true arm — a digit or `-`.  This module adds the scan-free tail's three links and the
merge's one, and assembles the `WalkDispatchResult.merge` the dispatch consumes.

## What the arm supplies

The tail's three calls are the same sub-calls the last entry's high-byte path makes
(`s2_value_pos`, `od_scalar_value`, `s2_after_value`), so `consumerTailSegEmptyAt`
serves both: its statement is at the tail's *entry* state, and the kind operand is the
one difference between them — `7` here (the numeral's), `0` there (the unclassified
byte's).  The prefix supplies the tail's source invariant, and the three call
contracts supply the answers and the appended record.

The merge's cells are the state's own: `%inc.i` and `%sp.i.0248` are `WalkInv.inc_reg`
and `WalkInv.depth_reg` at the merge, `%nep` is a `walkStaticRegs` pair read by
`WalkInv.regs`.  So the endpoint facts are clauses of the invariant at the state the
segment reaches, not separate supplies.

The price is the dispatch's own: `15 + 2 ≤ 32 · Δk + 8 · ΔA` at `Δk = 1` and
`ΔA = 0` (`entryPos G G.nep = 0`), i.e. `17 ≤ 32`, and the merge's *test* — `%k.2.i <
%nep` — is what classifies the outcome, not anything this module decides.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarPrefix
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seam state's two cells

The scan-free arm's test reads `%ee.1.i` and `%cond350.i`; at the tag test's true arm
the seam stored the bound at the first and `cond.end349.i` bound the second, so both are
the same number. -/

/-- `%ee.1.i` at the seam is the bound: `if.end372.i` stored `%cond350.i` there. -/
theorem scalarSeam_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarSeam C s x inc nep v ix b35).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [scalarSeam, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the seam is the same bound. -/
theorem scalarSeam_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (scalarSeam C s x inc nep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [scalarSeam, seamFin, scalarP37, scalarP39, scalarP41, scalarLand, scalarEndS,
    condEnd349OutAt, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- **The tail's source is at the merge's entry**: `%ee.1.i` and `%cond350.i` are one
number, so the scan's guard is `ult v v` and the walk leaves for `if.end473.i`. -/
theorem scalarEntry_pc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    (ScanEntry (scalarSeam C s x inc nep v ix b35) r₁ r₂ r₃ v v cA rdv xA).pc =
      "if.end473.i" := by
  show (if evalICmp .ult (BitVec.ofNat 64 v) (BitVec.ofNat 64 v) = 1 then
    "land.rhs457.i" else "if.end473.i") = "if.end473.i"
  rw [hlast_ult_self]
  rfl

/-- The merge's depth `phi`, read off the block's incoming list. -/
theorem scalar_phiSp :
    phiIncoming "if.end473.i" cleanupSpIncoming = some (.reg "%sp.i.0248") := by
  decide

/-- The merge's index `phi`, read off the block's incoming list. -/
theorem scalar_phiK :
    phiIncoming "if.end473.i" cleanupKIncoming = some (.reg "%inc.i") := by
  decide

/-- The tag test's true arm selects the numeral's kind, `7`. -/
theorem scalar_phiKind :
    phiIncoming "if.end372.i"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 7))) := by
  decide

/-- **The tail's segment at the seam, from the three call contracts.**  The same
composition as the last entry's high-byte path (`hlastTail_of_calls`), at the tag test's
true arm and the numeral's kind: the value-position call, the scalar call's emit arm and
the copy call, then the scan-free arm's three links. -/
theorem scalarTail_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (r₁ r₂ r₃ : CallOutcome)
    (hInvS : WalkInv G (ScalarC₁₁ C) (scalarSeam C s x inc nep v ix b35))
    {rdv : BitVec 32} {xA : BitVec 32}
    (hreadT : readBytes
      (writeBytes (scalarSeam C s x inc nep v ix b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x inc nep v ix b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4)) (scalarSeam C s x inc nep v ix b35).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x inc nep v ix b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4)) (scalarSeam C s x inc nep v ix b35).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (scalarSeam C s x inc nep v ix b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c, .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c, .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64) (htight : C.events.length ≤ C.k) (hklt : C.k < G.nep)
    (hv64 : v < 2 ^ 64)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next =
      some r₃) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (ScalarC₁₁ C)
        (scalarSeam C s x inc nep v ix b35)
        (TailCarryEnd (ScalarC₁₁ C) ev)
        (ScanEntry (scalarSeam C s x inc nep v ix b35) r₁ r₂ r₃ v v
          (BitVec.ofNat 32 7) rdv xA) 3 := by
  -- the value-position call's contract: the caller's memory comes back unchanged
  obtain ⟨r₁', hcall₁', hpost₁, _⟩ :=
    s2ValuePosContract.resolves (next := (scalarSeam C s x inc nep v ix b35).next) hpre₁
  obtain ⟨v₁, _, _, hmemV₁, _⟩ := hpost₁
  have hr₁ : r₁' = r₁ := Option.some.inj (hcall₁'.symm.trans hcall₁)
  rw [hr₁] at hmemV₁
  have hzreadJ : readBytes r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) := by
    rw [hmemV₁]; exact hzread
  -- the scalar call's contract: the record it appended, named here
  obtain ⟨r₂', hcall₂', hpost₂, _⟩ :=
    s2ScalarValueContract.resolves (next := r₁.next) hpre₂
  have hr₂ : r₂' = r₂ := Option.some.inj (hcall₂'.symm.trans hcall₂)
  rw [hr₂] at hpost₂
  obtain ⟨⟨_, _, _, _, _, _⟩, happPost⟩ := hpost₂
  obtain ⟨ev, happ₂⟩ := happPost hret₂
  -- the copy call's contract: the answer and the memory it leaves
  obtain ⟨r₃', hcall₃', hpost₃, _⟩ :=
    s2AfterValueContract.resolves (next := r₂.next) hpre₃
  have hr₃ : r₃' = r₃ := Option.some.inj (hcall₃'.symm.trans hcall₃)
  rw [hr₃] at hpost₃
  obtain ⟨_, _, _, _, _⟩ := hpost₃
  exact ⟨ev, Seg.measure (consumerTailSegEmptyAt (G := G) (C := ScalarC₁₁ C)
    (s := scalarSeam C s x inc nep v ix b35) r₁ r₂ r₃ ev v
    hInvS rfl "if.end372.i" "%kind404.i" (BitVec.ofNat 32 7)
    (.imm (.int 32 (BitVec.ofNat 32 7))) rdv xA rfl scalar_phiKind rfl
    (hInvS.regs ("%kind404.i", .ptr ((ScalarC₁₁ C).stage.tok + 16))
      (by simp [walkStaticRegs]))
    (hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hreadT hpre₁ hcall₁ hret₁ hbit0T hzreadJ
    (hInvS.regs ("%c.i", .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c)
      (by simp [walkStaticRegs]))
    (hInvS.regs ("%t352.i", .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok)
      (by simp [walkStaticRegs]))
    (hInvS.regs ("%z", .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z)
      (by simp [walkStaticRegs]))
    hcall₂ happ₂ hret₂ hev64
    (by have h1 := hInvS.evlen_le; have h2 := G.evRoom; have h3 := G.evcapLt; omega)
    htight hklt hpre₃ hcall₃
    (scalarSeam_ee C s x inc nep v ix b35) (scalarSeam_cond C s x inc nep v ix b35)
    hv64)⟩

/-! ### The arm's result

The prefix's eleven links, the tail's three and the merge's one, with the merge's own
test left to the classifier. -/

/-- **The scalar arm's dispatch result.**  The last entry's plain-value path: the
switch's default arm, the document's last byte's no-whitespace class, the tag test's
true arm, the three calls and the merge — one `merge` alternative of
`WalkDispatchResult`, whose index is `C.k + 1` (the last entry's) and whose price is
`15 + 2 ≤ 32`. -/
theorem scalarMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
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
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (r₁ r₂ r₃ : CallOutcome) {rdv : BitVec 32} {xA : BitVec 32}
    (hreadT : readBytes
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4))
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
        (BitVec.ofNat 64 (entryPos G C.k)) b35).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4))
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
        (BitVec.ofNat 64 (entryPos G C.k)) b35).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
        (natToBytes (7 : Nat) 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c, .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c, .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next =
      some r₃) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  -- the last index and the trace's tight count, from the head's own guard
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by rw [hblock])
  have hk : C.k + 1 = G.nep := by have := hInv.k_le; omega
  have htight : C.events.length ≤ C.k :=
    WalkInv.events_le_of_tight hInv
      (by rw [hblock]; exact walkEmitC_of_not_contains (by decide))
  -- the prefix: eleven links to the value-position call
  have hpre := scalarPrefixSeg (G := G) (C := C) (s := s) hInv hblock h8 h91 h44 h58 hne44
    hnot hread35 hb13 hb32 hbne32 hbit
  -- the tail: three links, at the prefix's endpoint
  obtain ⟨ev, htail⟩ := scalarTail_of_calls G C s x (BitVec.ofNat 64 (C.k + 1))
    (BitVec.ofNat 64 G.nep) G.n (BitVec.ofNat 64 (entryPos G C.k)) b35 r₁ r₂ r₃ hpre.inv'
    hreadT hpre₁ hcall₁ hret₁ hbit0T hzread hpre₂ hcall₂ hret₂ hev64 htight hklt
    (by have h := G.maxDoc; simp only [stage2MaxDocument] at h; omega) hpre₃ hcall₃
  -- the merge's step, at the state it names
  have htok : lookupName (ScanEntry (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1))
      (BitVec.ofNat 64 G.nep) G.n (BitVec.ofNat 64 (entryPos G C.k)) b35) r₁ r₂ r₃ G.n G.n
      (BitVec.ofNat 32 7) rdv xA).env "%t352.i" =
      some (.ptr (ScalarC₁₁ C).stage.tok) :=
    htail.inv'.regs ("%t352.i", .ptr (ScalarC₁₁ C).stage.tok) (by simp [walkStaticRegs])
  obtain ⟨sd, hlink, hsd⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := TailCarryEnd (ScalarC₁₁ C) ev)
      (s := ScanEntry (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k)) b35) r₁ r₂ r₃ G.n G.n (BitVec.ofNat 32 7)
        rdv xA) htail.inv' rfl htok
  -- the segment, counted at fifteen, at the merge state the link names
  let sE : State := ScanEntry (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1))
    (BitVec.ofNat 64 G.nep) G.n (BitVec.ofNat 64 (entryPos G C.k)) b35) r₁ r₂ r₃ G.n G.n
    (BitVec.ofNat 32 7) rdv xA
  let sM : State := { sE with pc := "cleanup478.i", pre := some sE.pc }
  have hlinkM : WalkLink (stage2Calls stage2SubCalls) G (TailCarryEnd (ScalarC₁₁ C) ev) sE
      { TailCarryEnd (ScalarC₁₁ C) ev with block := "cleanup478.i" } sM := by
    have h := hlink
    rw [show sd = sM from hsd] at h
    exact h
  let seg : WalkSegment (stage2Calls stage2SubCalls) G C s
      { TailCarryEnd (ScalarC₁₁ C) ev with block := "cleanup478.i" } sM (((11 + 3) + 1)) :=
    hpre.trans (htail.trans (WalkSegment.of_link hlinkM))
  -- the merge's cells are the invariant's at the endpoint
  have hinvE : WalkInv G { TailCarryEnd (ScalarC₁₁ C) ev with block := "cleanup478.i" } sM :=
    seg.inv'
  refine WalkDispatchResult.merge
    { TailCarryEnd (ScalarC₁₁ C) ev with block := "cleanup478.i" } sM (((11 + 3) + 1))
    C.sp (C.k + 1) "if.end473.i" (.reg "%sp.i.0248") (.reg "%inc.i")
    (BitVec.ofNat 64 G.nep) seg rfl rfl ?_ scalar_phiSp ?_ scalar_phiK ?_ ?_
    (by omega) ?_ hinvE.depth_cap hinvE.sp_le_wlen ?_
  · show sM.pre = some "if.end473.i"
    show (some sE.pc : Option String) = some "if.end473.i"
    rw [show sE.pc = "if.end473.i" from
      scalarEntry_pc C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
        (BitVec.ofNat 64 (entryPos G C.k)) b35 r₁ r₂ r₃ (BitVec.ofNat 32 7) rdv xA]
  · exact hinvE.depth_reg
  · exact hinvE.inc_reg
  · exact hinvE.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  · have hne : G.nep < 2 ^ 64 := by
      have h1 := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    show C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hne, ← hk]
  · -- the price: `15 + 2 ≤ 32 · 1 + 8 · 0`
    have hpos : entryPos G G.nep = 0 := walkEntryPos_at_nep G
    rw [hk, hpos]
    have hsub : G.nep - C.k = 1 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hsub, Nat.zero_sub,
      Nat.mul_zero, Nat.add_zero]
    omega

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scalarSeam_ee
#print axioms LeanLLVM.Refinement.WalkScope.scalarSeam_cond
#print axioms LeanLLVM.Refinement.WalkScope.scalarEntry_pc
#print axioms LeanLLVM.Refinement.WalkScope.scalarTail_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.scalarMerge_at

end WalkScope
end LeanLLVM.Refinement
