/-
The head path's arrival at the extra-token scan.

The walk's first revolution is a finite chain from the loop head `NodeBlock21` to the
scan's latch `while.body462.i`.  Four pieces make it, and this module joins them:

* `walkHeadChainA` — the head's high-byte fall-through to the token's end, ending at the
  named `HeadAC₆ C` / `headEndS C s x inc nep c ix`;
* `WalkLink.if_end372_i_at` — the token's end `if.end372.i` with its successor **named**,
  the seam that carries `%8` across it into the class-C span;
* `walkHeadChainC` — the nested pivots on `%8` to the value-position call;
* `consumer_tail_chain` — the three call consumers, restated as links, and
  `walkScanChain457_ws` — the scan's landing, its pivot and its range leaf.

**Why the seam has its own lemma.**  `if.end372.i`'s link states its successor
existentially (`WalkLink.if_end372_i`), because the block is six instructions and the
statement of its `denoteCode` belongs in the link rather than in its conclusion.  But a
chain that must be continued cannot be continued at an opaque state, and the next span
reads `%8` — a name the walk *carries* rather than one any `WalkInv` field binds
(`walkCarriedNames` lists it; `walkStaticRegs` does not).  So the party that consumes the
seam states it: `WalkLink.if_end372_i_at` names the target, exactly as
`WalkLink.NodeBlock21_at` names its own, and the class-C span's byte hypothesis is then a
fact about a name instead of about a variable.

**Why the tail is restated.**  `consumer_tail_seg` composes the three call links into a
`WalkSegment`, whose count is `3`.  A segment carries no links, and `WalkChain` has only
`nil` and `tail`, so nothing turns a segment back into a chain; `consumer_tail_chain`
therefore states the same three links at the same carries (`TailCarry₂`, `TailCarry₃`,
`TailCarryScan`) and the same states (`TailS₁`, `TailS₂`, `TailS₃`), reading the same
premises in the same order and adding nothing but the composition.
-/
import LeanLLVM.Refinement.JsonStage2WalkHeadChainA
import LeanLLVM.Refinement.JsonStage2WalkHeadChainC
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessFinish

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-! ### The seam: `if.end372.i` with its successor named

The block's run is the state `WalkLink.if_end372_i` builds internally — the `phi`'s cell,
the store's memory and the four comparison cells — so naming the target is naming the
`denoteCode` result the link already carries, and then the step is the same
`walkExecTerm_condbr` the other class-A instances use.
-/

/-- `if.end372.i`'s run, before the edge. -/
def seamFin (s : State) (e : BitVec 64) (b8 : BitVec 8) (tok : Nat) : State :=
  stateAt (("%or.cond677.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
      ("%or.cond524.i", .int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10))) ::
      ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
      ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
      ("%ee.1.i", .int 64 e) :: s.env)
    { s with mem := writeBytes s.mem (tok + 8) (natToBytes e.toNat 8) }

/-- `if.end372.i`'s target on the else arm: the run's state at the empty body's entry, the
block the class-C span of the head path starts from. -/
def seamS (s : State) (e : BitVec 64) (b8 : BitVec 8) (tok : Nat) : State :=
  { seamFin s e b8 tok with pc := "if.else387.i", pre := some s.pc }

/-- **`if.end372.i`'s target, named.**  The token's end `phi`, the store at `%end.i`, the
byte's two tests and the `or` that picks the edge — with the successor written down
instead of left existential, and the else arm taken.

This is the seam between the head's fall-through and the class-C span: naming the target
is what lets a chain continue there, and `%8` at that name is the next span's hypothesis. -/
theorem WalkLink.if_end372_i_at {calls : Calls} {m0 : Mem}
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
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "if.else387.i" } s' ∧
      s' = seamS s e b8 C.stage.tok := by
  obtain ⟨s', hl⟩ := WalkLink.if_end372_i (calls := calls) G C s hInv hblock hpre hin hv hend h8
  rw [show ({ C with block := (if (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1 then
      "if.then413.i" else "if.else387.i") } : WalkCarry G) =
      { C with block := "if.else387.i" } from by
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
      (env := ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' }) (d := "%cmp376.i") (a := "%8") 8
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
          exact walkLookup_cons_self "%cmp376.i" (.int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45)))
            (("%ee.1.i", .int 64 e) :: s.env))
      (by exact walkLookup_cons_self "%or.cond524.i" (.int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) (("%37", .int 8 (b8 + BitVec.ofNat 8 208)) :: ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) :: ("%ee.1.i", .int 64 e) :: s.env))]
    rfl
  have hden' : denoteCode calls walkIf_end372_i.instrs s =
      some (seamFin s e b8 C.stage.tok) := hden
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
  have hstep : LeanLLVM.step calls stage2Body s = .jump (seamS s e b8 C.stage.tok) := by
    rw [hstep0]
    rw [show (if (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1 then
      "if.then413.i" else "if.else387.i") = "if.else387.i" from by rw [hbit]; rfl]
    rfl
  exact Ctrl.jump.inj (hl.step.symm.trans hstep)

/-! ### The tail as links

`consumer_tail_seg`'s statement, at `WalkChain`.  The carries and the states are the
segment's own — `TailCarry₂`, `TailCarry₃`, `TailCarryScan` and `TailS₁`, `TailS₂`,
`TailS₃` — so the two statements differ in the composition and in nothing else. -/

/-- **The tail chain's statement**: the same premises as `ConsumerTailSeg`, composed into
a chain whose carries are its own and whose end state is `TailS₃`'s. -/
def ConsumerTailChain {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) (ei cd : Nat) : Prop :=
  ∀ (_hInv : WalkInv G C s) (_hblock : C.block = "if.then413.i")
    (p : String) (_reg : String) (c : BitVec 32) (op : Operand) (rdv : BitVec 32)
    (x : BitVec 32),
    s.pre = some p →
    phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op →
    evalOperand (stateAt s.env s) op = some (.int 32 c) →
    lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)) →
    lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) →
    readBytes (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) →
    s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next →
    stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r₁ →
    r₁.ret = .int 32 x →
    evalICmp .eq x (BitVec.ofNat 32 0) = 0 →
    readBytes r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) →
    lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c) →
    lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok) →
    lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z) →
    stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
       .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂ →
    s2ScalarValueAppend r₁.mem r₂.mem (TailCarry₂ C).stage.z ev.encodedBytes →
    r₂.ret = .int 32 (BitVec.ofNat 32 1) →
    G.ev < 2 ^ 64 → C.evlen < 2 ^ 64 → C.events.length < C.k →
    s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next →
    stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next = some r₃ →
    lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)) →
    lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
    cd - ei ≤ C.inner → ei < cd → cd < 2 ^ 64 →
    WalkChain (stage2Calls stage2SubCalls) G C s (TailCarryScan C ev)
      (TailS₃ (TailS₂ (TailS₁ s r₁ c rdv x) r₂) r₃ ei cd)

/-- **The tail, composed as links.**  The three call consumers from `if.then413.i`'s entry
to the scan's entry `land.rhs457.i`: the value-position call, the scalar call's emit arm
and the copy call, each at its own link, ending where `walkScanChain457_ws` starts.

The statement is `ConsumerTailSeg`'s, read as a chain: same premises, same carries, same
states, so a caller who holds the segment's premises holds this one's. -/
theorem consumer_tail_chain {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) (ei cd : Nat) :
    ConsumerTailChain G C s r₁ r₂ r₃ ev ei cd := by
  intro hInv hblock p reg c op rdv x hpre hinc hop hkind hrd hread hpre' hcall₁ hret₁
    hbit0 hzreadJ hc ht ho hcall₂ happ₂ hret₂ hev64 hevlen64 hlt hpre447 hcall₃ hei hcd
    hinner hlt2 hcd64
  -- 1. the value-position call
  have hx413 : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r →
      r.ret = .int 32 x := by
    intro r hr
    have h : r = r₁ := Option.some.inj (hr.symm.trans hcall₁)
    rw [h]; exact hret₁
  obtain ⟨r₁', s₁', hcall₁', hl₁, hs₁'⟩ := walkIfThen413_at (G := G) (C := C) (s := s)
    (p := p) (reg := reg) (x := x) (op := op) hInv hblock hpre hinc hop hkind hrd hread hpre'
    hx413
  have hr₁ : r₁' = r₁ := Option.some.inj (hcall₁'.symm.trans hcall₁)
  rw [hr₁] at hs₁'
  have hs₁ : s₁' = TailS₁ s r₁ c rdv x := hs₁'
  rw [hs₁] at hl₁
  rw [show { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
      then "if.then418.i" else "if.then425.i") } = TailCarry₂ C from by rw [hbit0]; rfl] at hl₁
  -- 2. the scalar call's emit arm
  obtain ⟨s₂', hl₂, hs₂'⟩ := walkIfThen425_emit_at (G := G) (C := TailCarry₂ C)
    (s := TailS₁ s r₁ c rdv x) hl₁.inv' rfl
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%c.i") _ _ (by decide)] using hc)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%t352.i") _ _ (by decide)] using ht)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%z") _ _ (by decide)] using ho)
    (by simpa only [TailS₁, stateAt] using hzreadJ)
    (by simpa only [TailS₁, stateAt] using hcall₂) happ₂ hret₂ hev64 hevlen64 hlt
  have hs₂ : s₂' = TailS₂ (TailS₁ s r₁ c rdv x) r₂ := hs₂'
  rw [hs₂] at hl₂
  -- 3. the copy call, at the scan's entry
  obtain ⟨r₃', s₃', hcall₃', hl₃, hs₃'⟩ := walkIfThen447_at (G := G) (C := TailCarry₃ C ev)
    (s := TailS₂ (TailS₁ s r₁ c rdv x) r₂) hl₂.inv' rfl
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%root_done.i") _ _ (by decide)] using hrd)
    (by simpa only [TailS₂, TailS₁, stateAt] using hpre447)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%ee.1.i") _ _ (by decide)] using hei)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%cond350.i") _ _ (by decide)] using hcd)
    hinner hlt2 hcd64
  have hr₃ : r₃' = r₃ := Option.some.inj (hcall₃'.symm.trans hcall₃)
  rw [hr₃] at hs₃'
  have hbit1 : evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = (1 : BitVec 1) := by
    have h1 : (BitVec.ofNat 64 ei).toNat < (BitVec.ofNat 64 cd).toNat := by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [show evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)
        = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)) from rfl,
      show BitVec.ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = true from
        (BitVec.ult_iff_toNat_lt).2 h1]
    rfl
  rw [show (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
      then "land.rhs457.i" else "if.end473.i") = "land.rhs457.i" from by rw [hbit1]; rfl] at hl₃
  have hs₃ : s₃' = TailS₃ (TailS₂ (TailS₁ s r₁ c rdv x) r₂) r₃ ei cd := hs₃'
  rw [hs₃] at hl₃
  exact WalkChain.tail hl₁ (WalkChain.tail hl₂ (WalkChain.tail hl₃
    (WalkChain.nil hl₃.inv')))



/-! ### The join's names

Each is the term two links meet at: the seam's carry, the two seam states, the tail's
start, the scan's entry and the latch the chain ends at.
-/

/-- The carry at `if.else387.i`: the head's end carry with the empty body's edge. -/
abbrev HeadSeamC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₆ C with block := "if.else387.i" }

/-- `walkHeadChainA`'s end state, named: the token's end `phi`'s selection and the two
words `cond.end349.i` stores. -/
def headEndS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) : State :=
  condEnd349OutAt (headAS₅ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)

/-- The seam's target: the token's end's run at the class-C span's entry. -/
def seamAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) : State :=
  seamS (headEndS C s x inc nep c ix) e b8 C.stage.tok

/-- The tail's start carry: the class-C span's target at `if.then413.i`. -/
abbrev TailStartC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  HeadC₄₁₃ (HeadSeamC C)

/-- The tail's start state: the class-C span's target, at the value-position call. -/
def TailStart {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8) : State :=
  HeadS413 (seamAt C s x inc nep c ix e b8) x1

/-- The scan's entry: the tail's end state at `land.rhs457.i`. -/
def ScanEntry (s₀ : State)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (c rdv : BitVec 32) (xA : BitVec 32) : State :=
  TailS₃ (TailS₂ (TailS₁ s₀ r₁ c rdv xA) r₂) r₃ ei cd

/-- The join's target carry: the scan's latch. -/
abbrev ScanLatchC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }

/-! ### The join -/

/-- **The head path's arrival at the extra-token scan.**  One chain from the loop head
`NodeBlock21` to the scan's latch `while.body462.i`: `walkHeadChainA` to the token's end,
the seam `WalkLink.if_end372_i_at` at its named target, `walkHeadChainC` through the
nested pivots, the tail's links to the scan's entry, and `walkScanChain457_ws` from the
landing to the latch.

The premises are each link's own.  The three at the seam are the ones a `denoteCode`
statement would otherwise hide — the `phi`'s selection, the stored word and the byte —
and `h8c` is the class-C span's byte read at the seam's *name*, which is what the seam
lemma makes expressible.  The tail arrives as its own chain (`consumer_tail_chain` at the
same terms): a segment carries no links, so the composition cannot cross one. -/
theorem walkHeadChainToScan {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep c ix : BitVec 64} {reg : String}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    (hpre5 : phiIncoming "sw.default.i"
      [("cond.true345.i", Operand.reg "%conv347.i"),
       ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav5 : lookupName (headAS₅ s x inc nep).env reg = some (.int 64 c))
    (hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt c ix = 0)
    {p : String} {op : Operand} {e : BitVec 64} {b8 : BitVec 8}
    (hpre6 : (headEndS C s x inc nep c ix).pre = some p)
    (hin6 : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some op)
    (hv6 : evalOperand (headEndS C s x inc nep c ix) op = some (.int 64 e))
    (hend6 : lookupName (headEndS C s x inc nep c ix).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (headEndS C s x inc nep c ix).env "%8" = some (.int 8 b8))
    (hbit6 : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    {x1 : BitVec 8}
    (h8c : evalOperand (seamAt C s x inc nep c ix e b8) (.reg "%8") = some (.int 8 x1))
    (hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord)
    {cA rdv : BitVec 32} {xA : BitVec 32} {ei cd : Nat}
    (hTail : WalkChain (stage2Calls stage2SubCalls) G (TailStartC C)
      (TailStart C s x inc nep c ix e b8 x1)
      (TailCarryScan (TailStartC C) ev)
      (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA))
    {idx : BitVec 64} {a q : Nat} {bs : List UInt8} {src : String} {sel : Operand}
    (hpreS : (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).pre = some src)
    (hincS : phiIncoming src
      [("while.body462.i", (Operand.reg "%inc463.i")),
       ("if.then447.i", (Operand.reg "%ee.1.i"))] = some sel)
    (hopS : evalOperand (stateAt (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).env (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA)) sel = some (.int 64 idx))
    (h3S : lookupName (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).env "%3" = some (.ptr a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).mem (a + (idx.signExtend 64).toNat) 1 = some bs)
    (hbsS : bytesToNat bs = q)
    (hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (TailStartC C) ev))
      (landRhs457OutAt (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q))
    {x47 : BitVec 8}
    (h47 : evalOperand (landRhs457OutAt (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q) (.reg "%47") = some (.int 8 x47))
    (hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (TailStartC C) ev))
      (ScanS₉₆ (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47))
    (hlatch : WalkLocal { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }
      (Latch462S (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47)) :
    ∃ (s' : State),
      WalkChain (stage2Calls stage2SubCalls) G C s (ScanLatchC C ev) s' := by
  -- the head's fall-through, to the token's end
  have hA : WalkChain (stage2Calls stage2SubCalls) G C s (HeadAC₆ C)
      (headEndS C s x inc nep c ix) :=
    walkHeadChainA (G := G) (C := C) (s := s) (hInv := hInv) (hblock := hblock)
      (h8 := h8) (hlt91 := hlt91) (hlt123 := hlt123) (hlt125 := hlt125)
      (hne125 := hne125) (hinc := hinc) (hnep := hnep) (hge := hge) (hpre5 := hpre5)
      (hav5 := hav5) (hidx5 := hidx5) (htok5 := htok5) (hgap5 := hgap5) (hugt := hugt)
  -- the seam, at its named target
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.if_end372_i_at (calls := stage2Calls stage2SubCalls) (G := G) (C := HeadAC₆ C)
      (s := headEndS C s x inc nep c ix) (WalkChain.inv_last hA) rfl
      (hpre := hpre6) (hin := hin6) (hv := hv6) (hend := hend6) (h8 := h8end)
      (hbit := hbit6)
  have hAB : WalkChain (stage2Calls stage2SubCalls) G C s (HeadSeamC C)
      (seamAt C s x inc nep c ix e b8) := by
    rw [hs₁] at hl₁
    exact hA.append (WalkChain.tail hl₁ (WalkChain.nil hl₁.inv'))
  -- the class-C span
  have hC : WalkChain (stage2Calls stage2SubCalls) G (HeadSeamC C)
      (seamAt C s x inc nep c ix e b8) (TailStartC C) (TailStart C s x inc nep c ix e b8 x1) :=
    walkHeadChainC (G := G) (C := HeadSeamC C) (s := seamAt C s x inc nep c ix e b8)
      (WalkChain.inv_last hAB) rfl h8c hc110 hc116 hceq116
  -- the tail's links, and the scan's landing
  have hCT : WalkChain (stage2Calls stage2SubCalls) G C s
      (TailCarryScan (TailStartC C) ev) (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) := (hAB.append hC).append hTail
  obtain ⟨s', hScan⟩ :=
    walkScanChain457_ws (calls := stage2Calls stage2SubCalls) (G := G)
      (C := TailCarryScan (TailStartC C) ev) (s := ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) (hInv := WalkChain.inv_last hCT)
      (hblock := rfl) (hpre := hpreS) (hinc := hincS) (hop := hopS) (h3 := h3S)
      (hpos := hpos) (hread := hreadS) (hbs := hbsS) (hloc105 := hloc105)
      (h47 := h47) (hbit := hbit47) (hws := hws47) (hloc96 := hloc96) (hlatch := hlatch)
  exact ⟨s', hCT.append hScan⟩

end WalkScope
end LeanLLVM.Refinement
