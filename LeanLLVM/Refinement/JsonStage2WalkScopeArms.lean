import LeanLLVM.Refinement.JsonStage2WalkScopeRecord

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The arm: `for.inc.i.i → for.body.i.i` -/

/-- The latch: `%inc.i.i = %i.029.i.i + 1`, the exit test `eq %inc.i.i,
%cond.i.i`, and the back edge to the header.  Two instructions, no memory. -/
def forIncBlock : Block :=
  { name := "for.inc.i.i",
    instrs := [
      Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i")
        (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i")
        (Operand.reg "%cond.i.i")],
    term := Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.i.i" "for.body.i.i" }

/-- The latch is the pinned body's block: the arm's proof is about `stage2Body`,
not about a transcription of it. -/
theorem forInc_find : stage2Body.findBlock "for.inc.i.i" = some forIncBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, forIncBlock]

/-- `%d = add i64 %a, 1` at the state's own environment.  `BlockEval`'s step is
stated at `stateAt env s`; this is the same step at `s`, which is the shape the
arm's state has. -/
theorem denoteCode_add_one (calls : Calls) (s : State) (d a : String) {x : BitVec 64}
    (ha : lookupName s.env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .add 64 (.reg a) (.imm (.int 64 (BitVec.ofNat 64 1))) :: is) s =
      denoteCode calls is (s.bind d (.int 64 (x + BitVec.ofNat 64 1))) := by
  simpa only [stateAt, State.bind] using
    (denoteCode_add_imm (calls := calls) (env := s.env) (s := s) (d := d) (a := a)
      (x := x) (c := BitVec.ofNat 64 1) ha is)

/-- `%d = icmp eq i64 %a, %b` at the state's own environment. -/
theorem denoteCode_icmp_eq (calls : Calls) (s : State) (d a b : String) {x y : BitVec 64}
    (ha : lookupName s.env a = some (.int 64 x))
    (hb : lookupName s.env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.icmp d .eq 64 (.reg a) (.reg b) :: is) s =
      denoteCode calls is (s.bind d (.int 1 (evalICmp .eq x y))) := by
  simpa only [stateAt, State.bind] using
    (denoteCode_icmp_eq_reg (calls := calls) (env := s.env) (s := s) (d := d) (a := a)
      (b := b) (x := x) (y := y) ha hb is)

/-- One step of the latch, at the state its back edge carries. -/
theorem forInc_denote {calls : Calls} (s : State) (i c : Nat)
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    denoteCode calls
      [Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i")
         (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
       Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i")
         (Operand.reg "%cond.i.i")] s =
      some (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))
            |>.bind "%exitcond.not.i.i" (.int 1 (0 : BitVec 1))) := by
  rw [denoteCode_add_one calls s "%inc.i.i" "%i.029.i.i" (x := BitVec.ofNat 64 i) hi]
  rw [denoteCode_icmp_eq calls
      (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 i + BitVec.ofNat 64 1)))
      "%exitcond.not.i.i" "%inc.i.i" "%cond.i.i"
      (x := BitVec.ofNat 64 i + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (by simp only [State.bind, lookupName_cons_self])
      (by
        simp only [State.bind]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hc)]
  have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add (n := 64) i 1]
  have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 c := by
    intro heq
    have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    have h2 : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [heq, h2] at h1
    omega
  simp only [hadd]
  rw [show evalICmp IPred.eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 from
    (evalICmp_eq_zero_iff _ _).mpr hne]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- The latch's terminator: at a clear exit test it jumps to the header and
records the latch as the predecessor. -/
theorem forInc_term {calls : Calls} (s : State) (i c : Nat)
    (hpc : s.pc = "for.inc.i.i")
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    step calls stage2Body s =
      .jump { (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
                "%exitcond.not.i.i" (.int 1 (0 : BitVec 1)) with
              pc := "for.body.i.i"
              pre := some "for.inc.i.i" } := by
  simp only [step, hpc, forInc_find, forIncBlock]
  rw [forInc_denote s i c hi hc hlt hcw]
  dsimp only
  rw [execTerm_condbr_zero _ _ _ _ _
      (by simp only [State.bind, evalOperand, lookupName_cons_self]) rfl]
  simp only [State.bind, hpc]

/-- **The smallest arm.**  From the invariant at the latch, one control step
reaches the header with the invariant preserved and the measure strictly smaller:
`k` is unchanged and the inner component goes from `c - i` to `c - (i + 1)`.

This is the feasibility test the scope asks for: the invariant is preserved field
for field (the block, the index, the cursors, the extents, the record in flight,
the refusal offset, the memory claim, and the local facts at the landing block),
and the measure's decrease is the arm's own arithmetic, not a hypothesis. -/
theorem forInc_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (i c : Nat)
    (hInv : WalkInv G C s) (hblock : C.block = "for.inc.i.i")
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hinner : c - i ≤ C.inner) (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧
      C'.stage = C.stage ∧
      C'.block = "for.body.i.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  -- the landing state and the carried data one inner iteration later
  let e : State :=
    { s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))
      |>.bind "%exitcond.not.i.i" (.int 1 (0 : BitVec 1)) with
      pc := "for.body.i.i"
      pre := some "for.inc.i.i" }
  let C' : WalkCarry G := { C with block := "for.body.i.i", inner := C.inner - 1 }
  have hpc : s.pc = "for.inc.i.i" := by rw [hInv.pc_eq, hblock]
  have hstep : step calls stage2Body s = .jump e := forInc_term s i c hpc hi hc hlt hcw
  have hk : lookupName e.env "%k.0.i249" = lookupName s.env "%k.0.i249" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  have hsp : lookupName e.env "%sp.i.0248" = lookupName s.env "%sp.i.0248" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  refine ⟨e, C', hstep, ?_, rfl, rfl, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := by rw [hk]; exact hInv.blockIndex
        k_le := hInv.k_le
        events_le := by
          show C.events.length ≤ C.k + walkEmitC "for.body.i.i"
          have h := hInv.events_le
          rw [hblock] at h
          have h1 : walkEmitC "for.inc.i.i" = 0 := walkEmitC_of_not_contains (by decide)
          have h2 : walkEmitC "for.body.i.i" = 0 := walkEmitC_of_not_contains (by decide)
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := by
          show C.inner - 1 ≤ walkInnerCap G
          have := hInv.inner_cap
          omega
        depth_cap := hInv.depth_cap
        depth_reg := by rw [hsp]; exact hInv.depth_reg
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes
        stBytes := hInv.stBytes
        ptrs := by
          dsimp only [e, State.bind]
          exact hInv.ptrs.bind_pair
            (a := "%inc.i.i") (b := "%exitcond.not.i.i")
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
        regs := by
          dsimp only [e, State.bind]
          exact hInv.regs.bind_pair
            (a := "%inc.i.i") (b := "%exitcond.not.i.i") (by decide) (by decide)
        iter := by
          dsimp only [e, State.bind]
          exact hInv.iter.bind_pair
            (a := "%inc.i.i") (b := "%exitcond.not.i.i")
            (va := .int 64 (BitVec.ofNat 64 (i + 1))) (vb := .int 1 (0 : BitVec 1))
            (by decide) (by decide)
        log_hash := by dsimp only [e]; exact hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        log_base := hInv.log_base
        log_dst := hInv.log_dst
        owned := hInv.owned
        root_slot := hInv.root_slot
        next_ge := hInv.next_ge
        frame := hInv.frame
        inc_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact hInv.inc_reg
        idx_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact hInv.idx_reg
        blockLocal := ?_ }
    dsimp only [WalkLocal, C']
    rw [if_neg (by decide), if_pos rfl]
    refine Or.inl ⟨i + 1, c, ?_, hlt, hcw, rfl, ?_⟩
    · show c - (i + 1) ≤ C.inner - 1
      omega
    dsimp only [e, State.bind]
    refine ⟨?_, ?_⟩
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
  · dsimp only [walkMeasure, C']
    exact Nat.add_lt_add_left (by omega) _
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]

/-- **The arm at its front door.**  Beside `WalkInv` the only hypothesis is the
latch's guard: no register read and no counter value is assumed.  The guard's
`i + 1 < c` is what `forInc_step` turns into the branch and the decrease. -/
theorem forInc_arm {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "for.inc.i.i")
    (hguard : ForIncGuard C s) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧
      C'.stage = C.stage ∧
      C'.block = "for.body.i.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, hlt, hcw, hi, hc⟩ := hguard
  exact forInc_step G C s i c hInv hblock hi hc hinner hlt hcw

/-! ### The four scans

Each scan's back edge has the same shape, and it is the smallest shape in the
body after the literal comparison: a latch that steps a counter by one, tests it
for equality against the scan's own bound, and — when the test is clear — jumps
back to the block that holds the counter's `phi`.  `while.body370.i → land.rhs.i`
(the whitespace skip), `while.body.i104 → land.rhs.i103` (the string scan),
`while.body76.i → land.rhs71.i` (the escape scan) and `while.body462.i →
land.rhs457.i` (the extra-token scan) are that block at four sets of names.

They read staged memory — each landing block loads a document byte — but none
writes it, so the memory claim is carried through unchanged, and the step is the
two instructions at the state's own environment.  The measure's outer factor is
the same on both sides because `k` is not read; the inner component falls by one.
-/

/-- A scan's latch, as a block: the counter steps by one, the bound is tested for
equality, and a clear test takes the back edge to `land`.  The `exit` arm is what
the test takes when the counter reaches the bound, and it is a different block in
each scan, so both successors are the edge's names. -/
def scanBlock (src inc phi test cond exit land : String) : Block :=
  { name := src,
    instrs := [
      Instr.binop inc BinOp.add 64 (Operand.reg phi)
        (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp test IPred.eq 64 (Operand.reg inc) (Operand.reg cond)],
    term := Term.condbr (Operand.reg test) exit land }

/-- The whitespace skip's latch is the pinned body's block. -/
theorem scanWhitespace_find :
    stage2Body.findBlock "while.body370.i" =
      some (scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The string scan's latch is the pinned body's block. -/
theorem scanString_find :
    stage2Body.findBlock "while.body.i104" =
      some (scanBlock "while.body.i104" "%inc.i105" "%ee.011.i" "%exitcond.not.i"
        "%cond.i" "cleanup474.i" "land.rhs.i103") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The escape scan's latch is the pinned body's block. -/
theorem scanEscape_find :
    stage2Body.findBlock "while.body76.i" =
      some (scanBlock "while.body76.i" "%inc77.i" "%s2.020.i" "%exitcond24.not.i"
        "%cond.i" "while.end78.i" "land.rhs71.i") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The extra-token scan's latch is the pinned body's block. -/
theorem scanExtraToken_find :
    stage2Body.findBlock "while.body462.i" =
      some (scanBlock "while.body462.i" "%inc463.i" "%q.0.i246" "%exitcond298.not"
        "%cond350.i" "if.end473.i" "land.rhs457.i") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The landing block's leading `phi`, read out of the pinned body, and the
operand it selects from the latch.  The outer `none` is a missing block or a
first instruction that is not a `phi`; the inner one is a predecessor the block
does not list.  The `#guard`s below are the instrument: each evaluates the body,
so a landing fact written for a predecessor or an increment the body does not
list fails at elaboration instead of being assumed. -/
def scanLandSelect (land src : String) : Option (Option Operand) :=
  match stage2Body.findBlock land with
  | none => none
  | some b =>
      match b.instrs.head? with
      | some (.phi _ _ inc) => some (phiIncoming src inc)
      | _ => none

-- The whitespace skip lands on a `phi` that selects `%inc371.i` from
-- `while.body370.i`.
#guard scanLandSelect "land.rhs.i" "while.body370.i" = some (some (.reg "%inc371.i"))

-- The string scan lands on a `phi` that selects `%inc.i105` from
-- `while.body.i104`.
#guard scanLandSelect "land.rhs.i103" "while.body.i104" = some (some (.reg "%inc.i105"))

-- The escape scan lands on a `phi` that selects `%inc77.i` from `while.body76.i`.
#guard scanLandSelect "land.rhs71.i" "while.body76.i" = some (some (.reg "%inc77.i"))

-- The extra-token scan lands on a `phi` that selects `%inc463.i` from
-- `while.body462.i`.
#guard scanLandSelect "land.rhs457.i" "while.body462.i" = some (some (.reg "%inc463.i"))

/-! #### `WalkLocal` at the scans' blocks

Each unfolding names the branch `WalkLocal` takes at that block, so an arm reads
its register facts from the invariant and writes the landing facts back into it
without unfolding the whole chain. -/

/-- `WalkLocal` at the whitespace skip's latch. -/
theorem WalkLocal.whitespace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body370.i") :
    WalkLocal C s = ScanCount s "%ee.0.i238" "%cond350.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the whitespace skip's landing block. -/
theorem WalkLocal.whitespaceLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs.i") :
    WalkLocal C s = (ScanLanded s "while.body370.i" "%inc371.i" "%cond350.i" C.inner ∨
      ScanEntered s "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner) := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the string scan's latch. -/
theorem WalkLocal.stringScan {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body.i104") :
    WalkLocal C s = ScanCount s "%ee.011.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the string scan's landing block.  The third disjunct is `ScanEmpty`:
the scan's latch branches out of the loop on the increment that reaches the bound, and a
condbr link needs `WalkLocal` at the untaken arm, so at `%inc.i105 = %cond.i` this
clause would otherwise be uninhabited — see the definition's docstring. -/
theorem WalkLocal.stringScanLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs.i103") :
    WalkLocal C s = (ScanLanded s "while.body.i104" "%inc.i105" "%cond.i" C.inner ∨
      ScanEntered s "cond.end.i96" "%idxprom.i" "%cond.i" C.inner ∨
      ScanEmpty s "%inc.i105" "%cond.i") := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the escape scan's latch. -/
theorem WalkLocal.escape {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body76.i") :
    WalkLocal C s = ScanCount s "%s2.020.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the escape scan's landing block. -/
theorem WalkLocal.escapeLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "land.rhs71.i") :
    WalkLocal C s = (ScanLanded s "while.body76.i" "%inc77.i" "%cond.i" C.inner ∨
      ScanEntered s "if.end67.i" "%ee.0.lcssa.i" "%cond.i" C.inner) := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the extra-token scan's latch. -/
theorem WalkLocal.extraToken {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body462.i") :
    WalkLocal C s = ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the extra-token scan's landing block.  The third disjunct is
`ScanEmpty`: `land.rhs457.i` is reachable with `%ee.1.i = %cond350.i`, where the scan has
no bytes — see the definition's docstring. -/
theorem WalkLocal.extraTokenLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs457.i") :
    WalkLocal C s = (ScanLanded s "while.body462.i" "%inc463.i" "%cond350.i" C.inner ∨
      ScanEntered s "if.then447.i" "%ee.1.i" "%cond350.i" C.inner ∨
      ScanEmpty s "%ee.1.i" "%cond350.i") := by
  simp [WalkLocal, h]

/-- The whitespace skip's register facts, out of the invariant. -/
theorem WalkInv.whitespace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body370.i") :
    ScanCount s "%ee.0.i238" "%cond350.i" C.inner := by
  simpa [WalkLocal.whitespace hblock] using h.blockLocal

/-- The string scan's register facts, out of the invariant. -/
theorem WalkInv.stringScan {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body.i104") :
    ScanCount s "%ee.011.i" "%cond.i" C.inner := by
  simpa [WalkLocal.stringScan hblock] using h.blockLocal

/-- The escape scan's register facts, out of the invariant. -/
theorem WalkInv.escape {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body76.i") :
    ScanCount s "%s2.020.i" "%cond.i" C.inner := by
  simpa [WalkLocal.escape hblock] using h.blockLocal

/-- The extra-token scan's register facts, out of the invariant. -/
theorem WalkInv.extraToken {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body462.i") :
    ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
  simpa [WalkLocal.extraToken hblock] using h.blockLocal

/-! #### The scans' steps -/

/-- A scan's step, at the state's own environment: the counter increments and the
bound is tested for equality.  The equality is false because the counter is still
short of the bound, so the latch's test is clear and its back edge is the edge it
takes. -/
theorem scan_denote (calls : Calls) (s : State) (inc phi test cond : String) (i c : Nat)
    (hinc_cond : inc ≠ cond)
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    denoteCode calls
      [Instr.binop inc BinOp.add 64 (Operand.reg phi)
         (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
       Instr.icmp test IPred.eq 64 (Operand.reg inc) (Operand.reg cond)] s =
      some ((s.bind inc (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
        test (.int 1 (0 : BitVec 1))) := by
  rw [denoteCode_add_one calls s inc phi (x := BitVec.ofNat 64 i) hi]
  rw [denoteCode_icmp_eq calls
      (s.bind inc (.int 64 (BitVec.ofNat 64 i + BitVec.ofNat 64 1)))
      test inc cond
      (x := BitVec.ofNat 64 i + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (by simp only [State.bind, lookupName_cons_self])
      (by
        simp only [State.bind]
        rw [lookupName_cons_ne _ _ hinc_cond]
        exact hc)]
  have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add (n := 64) i 1]
  have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 c := by
    intro heq
    have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    have h2 : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [heq, h2] at h1
    omega
  simp only [hadd]
  rw [show evalICmp IPred.eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 from
    (evalICmp_eq_zero_iff _ _).mpr hne]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- A scan's terminator: a clear test jumps to the landing block, binding the
increment and naming the latch as the predecessor. -/
theorem scan_term {calls : Calls} (s : State) (i c : Nat)
    (src land phi inc test cond exit : String)
    (hpc : s.pc = src)
    (hfind : stage2Body.findBlock src = some (scanBlock src inc phi test cond exit land))
    (hinc_cond : inc ≠ cond)
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    step calls stage2Body s =
      .jump { ((s.bind inc (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
                test (.int 1 (0 : BitVec 1))) with
              pc := land
              pre := some src } := by
  simp only [step, hpc, hfind, scanBlock]
  rw [scan_denote calls s inc phi test cond i c hinc_cond hi hc hlt hcw]
  dsimp only
  rw [execTerm_condbr_zero _ _ _ _ _
      (by simp only [State.bind, evalOperand, lookupName_cons_self]) rfl]
  simp only [State.bind, hpc]

/-- **A scan's arm.**  From the invariant at a scan's latch, one control step
reaches that scan's landing block with every carried field preserved, the extents
and the memory untouched, and the measure strictly smaller: `k` is unchanged, so
the outer factor is the same, and the inner component falls from `c - i` to
`c - (i + 1)`.

The landing block's local facts are the last hypothesis' content: the caller
supplies them from the landing block's own `WalkLocal` branch, so the arm is
about the block the body jumps to and not about an assumed landing. -/
theorem scan_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (i c : Nat) (src land phi inc test cond exit : String)
    (hInv : WalkInv G C s) (hblock : C.block = src)
    (hfind : stage2Body.findBlock src = some (scanBlock src inc phi test cond exit land))
    (hinc_cond : inc ≠ cond) (htest_cond : test ≠ cond) (htest_inc : test ≠ inc)
    (hinc_k : inc ≠ "%k.0.i249") (htest_k : test ≠ "%k.0.i249")
    (hinc_sp : inc ≠ "%sp.i.0248") (htest_sp : test ≠ "%sp.i.0248")
    (hincN : ¬ inc = "%3" ∧ ¬ inc = "%5" ∧ ¬ inc = "%k11.i" ∧ ¬ inc = "%ctype.i"
      ∧ ¬ inc = "%cst.i" ∧ ¬ inc = "%hash1.i.i")
    (htestN : ¬ test = "%3" ∧ ¬ test = "%5" ∧ ¬ test = "%k11.i" ∧ ¬ test = "%ctype.i"
      ∧ ¬ test = "%cst.i" ∧ ¬ test = "%hash1.i.i")
    (hincS : walkFreshName inc) (htestS : walkFreshName test)
    (hincI7 : inc ≠ "%7") (hincI8 : inc ≠ "%8")
    (htestI7 : test ≠ "%7") (htestI8 : test ≠ "%8")
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hinner : c - i ≤ C.inner) (hlt : i + 1 < c) (hcw : c < 2 ^ 64)
    (hland : ∀ (e : State), e.pre = some src →
      lookupName e.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) →
      lookupName e.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
      WalkLocal (G := G) { C with block := land, inner := C.inner - 1 } e) :
    ∃ (e : State),
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := land, inner := C.inner - 1 } e ∧
      walkMeasure G { C with block := land, inner := C.inner - 1 } < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  have hpc : s.pc = src := by rw [hInv.pc_eq, hblock]
  let e : State :=
    { ((s.bind inc (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
        test (.int 1 (0 : BitVec 1))) with
      pc := land
      pre := some src }
  have hstep : step calls stage2Body s = .jump e :=
    scan_term s i c src land phi inc test cond exit hpc hfind hinc_cond hi hc hlt hcw
  have hinc : lookupName e.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_inc, lookupName_cons_self]
  have hcond : lookupName e.env cond = some (.int 64 (BitVec.ofNat 64 c)) := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_cond, lookupName_cons_ne _ _ hinc_cond]
    exact hc
  have hk : lookupName e.env "%k.0.i249" = lookupName s.env "%k.0.i249" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_k, lookupName_cons_ne _ _ hinc_k]
  have hsp : lookupName e.env "%sp.i.0248" = lookupName s.env "%sp.i.0248" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_sp, lookupName_cons_ne _ _ hinc_sp]
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := by
          show C.events.length ≤ C.k + walkEmitC land
          have h := hInv.events_le
          rw [hblock] at h
          have hle := (walkEmitC_condbr_le
            (B := scanBlock src inc phi test cond exit land)
            (findBlockList_mem hfind) rfl).2
          simp only [scanBlock] at hle
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := by
          show C.inner - 1 ≤ walkInnerCap G
          have := hInv.inner_cap
          omega
        depth_cap := hInv.depth_cap
        depth_reg := by rw [hsp]; exact hInv.depth_reg
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes
        stBytes := hInv.stBytes
        ptrs := by
          dsimp only [e, State.bind]
          exact hInv.ptrs.bind_pair (a := inc) (b := test) hincN htestN
        regs := by
          dsimp only [e, State.bind]
          exact hInv.regs.bind_pair (a := inc) (b := test) hincS.1 htestS.1
        iter := by
          dsimp only [e, State.bind]
          exact hInv.iter.bind_pair (a := inc) (b := test)
            (va := .int 64 (BitVec.ofNat 64 (i + 1))) (vb := .int 1 (0 : BitVec 1))
            ⟨hincI7, hincI8, hincS.2.2.1⟩ ⟨htestI7, htestI8, htestS.2.2.1⟩
        log_hash := by dsimp only [e]; exact hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        log_base := hInv.log_base
        log_dst := hInv.log_dst
        owned := by dsimp only [e]; exact hInv.owned
        root_slot := by dsimp only [e]; exact hInv.root_slot
        next_ge := hInv.next_ge
        frame := ?_
        inc_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ htestS.2.1, lookupName_cons_ne _ _ hincS.2.1]
          exact hInv.inc_reg
        idx_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne (k := test) (n := "%idxprom.i") _ _ htestS.2.2.2,
            lookupName_cons_ne (k := inc) (n := "%idxprom.i") _ _ hincS.2.2.2]
          exact hInv.idx_reg
        blockLocal := ?_ }
    · rw [hk]; exact hInv.blockIndex
    · dsimp only [e]; exact hInv.frame
    · exact hland e rfl hinc hcond
  · dsimp only [walkMeasure]
    exact Nat.add_lt_add_left (by omega) _
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]


/-! ### The exit

Both exit shapes store the walk's report to the caller's slots: `s2_walk.exit`
writes `ndst ← alen` and `nev ← evlen` and returns `1`; `if.then` writes the same
two and `err ← eoff` and returns `0`.  Those stores are the wrapper's and are
pinned in `JsonStage2IR`; `JsonStage2Body`'s `stage2Report` and
`stage2Run_boundary` are their effect.  What the exits read off the loop is the
report's clauses, and `WalkInv.report` is those clauses at the carry — the same
statement at both shapes, because the shapes differ in the wrapper's stores and
not in what the walk left.

The two clauses below that the invariant did not carry are `alen_ge` (the report's
`arenaGe`, the append-only half of the arena cursor) and, before this slice,
`inner_cap`.  Both are stated where their value is produced — the arena appends
and the loop head — and both are preserved by every arm that leaves the field
alone. -/

/-- A byte inside a present region is present. -/
theorem present_of_hasBytes {m : Mem} {a n x : Nat} (h : HasBytes m a n)
    (hlo : a ≤ x) (hhi : x < a + n) : present m x := by
  obtain ⟨vs, hvs⟩ := h
  have := LeanLLVM.readBytes_some_present m a n vs hvs (x - a) (by omega)
  simpa [show a + (x - a) = x by omega] using this

/-- **The report's clauses, read off the invariant.**  The seven numbers and the
two halves of the memory claim `Stage2Run` records from `arenaGe` onwards: both
cursors and their two-sided growth bounds, the last reserve's slack, the refusal
offset, presence at `stage2ReportPresent` (the extents the run leaves written), and
silence outside `stage2ReportFrame` (those extents plus the stack interval).

Presence comes from `WalkInv.owned` by coverage: the staged extents the run
carries are the geometry's, and `alen ≤ ndst0 + n`, `evlen ≤ evcap` put the
report's two prefixes inside them.

Silence is the invariant's frame at the same interval shape.  The report's stack
region ends at `stage2StackEnd G.next0 s.next` — the five bootstrap slots when
the walk has not passed them, the walk's cursor otherwise — and the invariant's
frame is the cursor's interval (`walkWideAt`).  The two are the same entry at two
ends, so the record's frame follows by widening the interval to that end
(`walkWideAt_le`), with no hypothesis on the cursor: the end carries it. -/
theorem WalkInv.report {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    G.ndst0 ≤ C.alen ∧
      C.alen ≤ G.ndst0 + G.n ∧
      G.nev0 ≤ C.evlen ∧
      C.evlen ≤ G.nev0 + stage2RecordBytes * G.n ∧
      C.alen + stage2ArenaReserve ≤ G.dstcap ∧
      C.eoff ≤ G.n ∧
      (∀ a, inRegions (stage2ReportPresent G.dst C.alen
        G.ev C.evlen G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) a → present s.mem a) ∧
      UnchangedOutside m0 s.mem
        (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst
          G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s
          C.stage.z C.stage.e C.stage.d G.next0 (stage2StackEnd G.next0 s.next)) := by
  have hle : C.alen ≤ G.ndst0 + G.n := h.alen_le
  have hev : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := h.evlen_le
  have hevcap : C.evlen ≤ G.evcap := le_trans hev G.evRoom
  have hstage : ∀ r ∈ walkStaged G C, HasBytes s.mem r.1 r.2 := h.owned
  have hroom := G.arenaRoom
  refine ⟨h.alen_ge, hle, ?_, hev, by omega, h.eoff_le, ?_, ?_⟩
  · rw [h.evlen_eq]
    exact Nat.le_add_right _ _
  · intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    have hcov : ∃ q ∈ walkStaged G C, q.1 ≤ a ∧ a < q.1 + q.2 := by
      simp only [stage2ReportPresent, stage2Writes, stage2ReportScratch] at hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_cons.mp hr with rfl | hr1
        · exact ⟨(G.dst, G.ndst0 + G.n + stage2ArenaReserve),
            by simp [walkStaged], by omega, by omega⟩
        · rcases List.mem_cons.mp hr1 with rfl | hr2
          · exact ⟨(G.ndst, 8), by simp [walkStaged], hlo, hhi⟩
          · rcases List.mem_cons.mp hr2 with rfl | hr3
            · exact ⟨(G.ev, G.evcap), by simp [walkStaged], hlo, by omega⟩
            · rcases List.mem_cons.mp hr3 with rfl | hr4
              · exact ⟨(G.nev, 8), by simp [walkStaged], hlo, hhi⟩
              · rcases List.mem_cons.mp hr4 with rfl | hnil
                · exact ⟨(G.err, 8), by simp [walkStaged], hlo, hhi⟩
                · exact absurd hnil (by simp)
      · exact ⟨r, by simp [walkStaged, stage2ReportScratch, hr], hlo, hhi⟩
    obtain ⟨q, hq, hqlo, hqhi⟩ := hcov
    exact present_of_hasBytes (hstage q hq) hqlo hqhi
  · refine UnchangedOutside.of_covered
      (walkWideAt_le (C := C) (n := s.next - G.next0)
        (n' := stage2StackEnd G.next0 s.next - G.next0) (by
          have hge := h.next_ge
          have hmax := le_stage2StackEnd G.next0 s.next
          omega) h.frame) ?_
    intro r hr
    simp only [walkWideAt, stage2ReportFrame, stage2ReportPresent, stage2Writes,
      stage2ReportScratch] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_cons.mp hr with rfl | hr1
        · exact ⟨(G.dst, C.alen + stage2ArenaReserve),
            by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
            le_rfl, by omega⟩
        · rcases List.mem_cons.mp hr1 with rfl | hnil
          · exact ⟨(G.ev, C.evlen),
              by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
              le_rfl, le_rfl⟩
          · exact absurd hnil (by simp)
      · exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), le_rfl, le_rfl⟩
    · rcases List.mem_cons.mp hr with rfl | hnil
      · exact ⟨(G.next0, stage2StackEnd G.next0 s.next - G.next0),
          List.mem_append_right _ (List.mem_cons_self ..), le_rfl, by
            have hge := h.next_ge
            have hmax := le_stage2StackEnd G.next0 s.next
            omega⟩
      · exact absurd hnil (by simp)

end LeanLLVM.Refinement
