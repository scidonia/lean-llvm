/-
# The string opener above depth zero: the marker links, and the key-true tail

`HcontArm.twoEntry` is the standalone string at the loop head's *depth-zero* entry:
`if.then219.i`'s depth test sends it to `if.end245.i` and the key bit is the
`if.then219.i` edge's zero.  The same byte `34` at a positive depth is the class the
census names and no arm covered: the same test sends the run to `land.lhs.true.i`,
which reads the type stack's byte at `%sp - 1` and branches to `if.then231.i`, whose
own read of the state stack's byte at the same index is the key bit the nest's `phi`
selects at `if.end245.i`.  From there the route rejoins the two-entry path's blocks —
`if.end256.i`'s reservation, the body's call, the answer's own tests, the record and
the merge — with one difference at the end: a true key takes `if.then330.i`, which
pushes the container's byte, instead of `if.else334.i`'s write-back.

This module states that route's two halves:

* **the two marker links, named** — `WalkLink.land_lhs_true_i` and
  `WalkLink.if_then231_i` conclude `∃ s', WalkLink … s'`, and a composition reads
  the next block's hypotheses at the state the previous one left.  `walkStackMarkerStep`
  names `land.lhs.true.i`'s successor (the five-instruction marker shape), and
  `if.then231.i`'s four-instruction read gets its own step.  The marker reads are
  `%ctype.i`'s and `%cst.i`'s bytes at `%sp - 1`, which the invariant's
  `tyBytes`/`stBytes` clauses supply at `%sp - 1 < wlen`.
* **`if.end245.i` onwards, key-true** — the merge's edge, the reservation, the body's
  call (supplied: `s2StringBodyPre`'s producer is the string staging, the row the
  residual table lists as G7), the answer's tests, the record, and the key's own
  branch to `cleanup478.i`.

The refusal the same nest can take is the key's other value: `%or.cond523.i` is the
key bit selected against the callee's answer, so a clear key with a refusing answer
leaves `if.end245.i` for `if.then249.i`, whose offset store and copy are the refusal
arm.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### `land.lhs.true.i`'s successor, named

The block is the layer's five-instruction marker shape (`walkStackMarkerStep`), read
at `%ctype.i` with `c = -1`, so its cells are `walkMarkerEnv`'s and its edge is the
byte's comparison with the brace's marker `1`. -/

/-- The five cells `land.lhs.true.i` binds: `%sp - 1`, its zero-extension, the type
stack's address, its byte and the comparison. -/
abbrev deepLandEnv (s : State) (sp ct : Nat) (b : UInt8) : Env :=
  walkMarkerEnv "%sub225.i" "%idxprom226.i" "%arrayidx227.i" "%27" "%cmp229.i"
    (BitVec.ofNat 32 sp) (BitVec.ofNat 32 4294967295) ct b.toNat
    (BitVec.ofNat 8 1) s.env

/-- The marker's comparison: the type stack's byte at `%sp - 1` is `1`. -/
abbrev deepLandBit (b : BitVec 8) : BitVec 1 :=
  evalICmp .eq b (BitVec.ofNat 8 1)

/-- **The state `land.lhs.true.i` leaves**: the five cells, and the edge its
comparison names — `if.then231.i` when the byte is the brace's marker, `if.end245.i`
otherwise. -/
def deepLandS (s : State) (sp ct : Nat) (b : UInt8) : State :=
  { stateAt (deepLandEnv s sp ct b) s with
    pc := (if deepLandBit (BitVec.ofNat 8 b.toNat) = 1 then "if.then231.i"
      else "if.end245.i"),
    pre := some s.pc }

/-- **`land.lhs.true.i`'s target, named.**  The marker shape's step
(`walkStackMarkerStep`) and the class's link, identified by `Ctrl.jump`'s
injectivity.  The read is the type stack's byte at `%sp - 1`, which the invariant
supplies at `%sp - 1 < wlen` (`WalkInv.tyBytes`). -/
theorem walkLandLhsTrue_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.lhs.true.i")
    {sp ct : Nat} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s
        { C with block := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
            then "if.then231.i" else "if.end245.i") } s' ∧
      s' = deepLandS s sp ct b := by
  obtain ⟨s', hl⟩ :=
    WalkLink.land_lhs_true_i (calls := calls) G C s hInv hblock hsp hct hq63 hread
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkLand_lhs_true_i := by
    rw [hInv.pc_eq, hblock]; exact walkLand_lhs_true_i_find
  have hstep := walkStackMarkerStep (calls := calls) (s := s)
    (B := walkLand_lhs_true_i)
    (gg := "%sub225.i") (zx := "%idxprom226.i") (ap := "%arrayidx227.i")
    (ld := "%27") (d := "%cmp229.i") (base := "%ctype.i")
    (tl := "if.then231.i") (fl := "if.end245.i")
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 4294967295) (a := ct)
    (one := BitVec.ofNat 8 1) (bs := [b]) (q := b.toNat)
    hfind rfl rfl hsp hct (by decide) (by decide) hq63 hread
    (bytesToNat_singleton b) (walkBitVec1_zero_or_one _)
  have hEq : s' = deepLandS s sp ct b :=
    Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)
  exact hEq

/-! ### `if.then231.i`'s successor, named

`if.then231.i` reads the *state* stack's byte at the same `%idxprom226.i`, masks the
two container kinds' bits (`&&& 251`) and compares the result with zero.  Its term is
an unconditional branch to `if.end245.i`, and the cell it binds is `%or.cond.i` — the
`if.end245.i` `phi`'s `if.then231.i` operand. -/

/-- The four cells `if.then231.i` binds: the state stack's address, its byte, the
masked byte and the comparison. -/
abbrev deepKindEnv (s : State) (cs q : Nat) (b : UInt8) : Env :=
  cells [("%or.cond.i", .int 1 (evalICmp .eq
      (BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251) (BitVec.ofNat 8 0))),
    ("%29", .int 8 (BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251)),
    ("%28", .int 8 (BitVec.ofNat 8 b.toNat)),
    ("%arrayidx235.i", .ptr (cs + q))] s.env

/-- **The state `if.then231.i` leaves**: the four cells at `if.end245.i`. -/
def deepKindS (s : State) (cs q : Nat) (b : UInt8) : State :=
  { stateAt (deepKindEnv s cs q b) s with pc := "if.end245.i", pre := some s.pc }

/-- **`if.then231.i`'s target, named.**  The block's own run (`gep`, `load`, `and`,
`icmp`) and its unconditional branch, identified with the class's link by
`Ctrl.jump`'s injectivity.  The read is the state stack's byte at `%sp - 1`
(`WalkInv.stBytes`). -/
theorem walkIfThen231_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then231.i")
    {cs q : Nat} {b : UInt8}
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hidx : lookupName s.env "%idxprom226.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (cs + q) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "if.end245.i" } s' ∧
      s' = deepKindS s cs q b := by
  obtain ⟨s', hl⟩ := WalkLink.if_then231_i G C s hInv hblock hcs hidx hq63 hread
  refine ⟨s', hl, ?_⟩
  have hden : denoteCode calls walkIf_then231_i.instrs s =
      some (stateAt (deepKindEnv s cs q b) s) := by
    simp only [walkIf_then231_i, deepKindEnv]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s)
      (d := "%arrayidx235.i") (base := "%cst.i") (off := "%idxprom226.i") (a := cs)
      (idx := BitVec.ofNat 64 q) hcs hidx (by rw [sExt_ofNat64 hq63]; exact hq63)]
    rw [sExt_ofNat64 hq63]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx235.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%28") (p := "%arrayidx235.i") (a := cs + q) (by simp [lookupName]) hread]
    rw [denoteCode_and_imm_w (calls := calls)
      (env := ("%28", .int 8 (BitVec.ofNat 8 b.toNat)) ::
        ("%arrayidx235.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%29") (a := "%28") (w := 8) (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 251) (by simp [lookupName])]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%29", .int 8 (BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251)) ::
        ("%28", .int 8 (BitVec.ofNat 8 b.toNat)) ::
        ("%arrayidx235.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%or.cond.i") (a := "%29") 8
      (x := BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251) (c := BitVec.ofNat 8 0)
      (by simp [lookupName])]
    rfl
  have hfind : stage2Body.findBlock s.pc = some walkIf_then231_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_then231_i_find
  have hterm : walkIf_then231_i.term = Term.br "if.end245.i" := rfl
  have hstep : LeanLLVM.step calls stage2Body s =
      .jump { stateAt (deepKindEnv s cs q b) s with
        pc := "if.end245.i", pre := some s.pc } := by
    simp only [LeanLLVM.step, hfind, hden, hterm, execTerm]
    rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-! ### `if.then330.i`'s successor, named

The key-true branch's last hop: `%sp - 1`'s state byte is set to `1` and the run
rejoins the merge.  The link is `WalkLink.if_then330_i`'s; the state it leaves is named
here because the merge's two `phi` selections are read *at* it (`sd.pre` is
`if.then330.i` and `%inc208.i` is the index). -/

/-- **The state `if.then330.i` leaves**: the three cells, the state stack's byte at
`%sp - 1` set to `1`, and the merge's edge. -/
def walkIfThen330OutAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : State :=
  { (stateAt (cells [
      ("%arrayidx333.i", .ptr (C.stage.cst + (C.sp - 1))),
      ("%idxprom332.i", .int 64 (BitVec.ofNat 64 (C.sp - 1))),
      ("%sub331.i", .int 32 (BitVec.ofNat 32 (C.sp - 1)))] s.env)
      { s with mem := writeBytes s.mem (C.stage.cst + (C.sp - 1)) (natToBytes (BitVec.ofNat 8 1).toNat 1) }) with
    pc := "cleanup478.i", pre := some s.pc }

/-- **`if.then330.i`'s target, named.**  The link with the successor's state exposed, so
the merge's `phi` selections can be read at it. -/
theorem walkIfThen330_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then330.i") (hsp1 : 1 ≤ C.sp) :
    ∃ s', WalkLink calls G C s { C with
        block := "cleanup478.i",
        stMap := fun i => if i = C.sp - 1 then
          (natToBytes (BitVec.ofNat 8 1).toNat 1).getD 0 0 else C.stMap i } s' ∧
      s' = walkIfThen330OutAt G C s := by
  obtain ⟨s', hl⟩ := WalkLink.if_then330_i G C s hInv hblock hsp1
  refine ⟨s', hl, ?_⟩
  have hsp32 : C.sp < 2 ^ 32 := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h
    omega
  have hpred32 : C.sp - 1 < 2 ^ 32 := by omega
  have hpred63 : C.sp - 1 < 2 ^ 63 := by omega
  have hden : denoteCode calls walkIf_then330_i.instrs s =
      some (stateAt (cells [
        ("%arrayidx333.i", .ptr (C.stage.cst + (C.sp - 1))),
        ("%idxprom332.i", .int 64 (BitVec.ofNat 64 (C.sp - 1))),
        ("%sub331.i", .int 32 (BitVec.ofNat 32 (C.sp - 1)))] s.env)
        { s with mem := writeBytes s.mem (C.stage.cst + (C.sp - 1)) (natToBytes (BitVec.ofNat 8 1).toNat 1) }) := by
    dsimp only [walkIf_then330_i]
    rw [← stateAt_self s]
    rw [walkDenoteCode_add_imm_w calls s.env s "%sub331.i" "%sp.i.0248" 32
      (c := BitVec.ofNat 32 4294967295) hInv.depth_reg
      [Instr.zext "%idxprom332.i" 32 64 (.reg "%sub331.i"),
       Instr.gep "%arrayidx333.i" (.int 8) (.reg "%cst.i") (.reg "%idxprom332.i"),
       Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")]]
    rw [walkOfNat32_add_pred hsp1 hsp32]
    rw [denoteCode_zext32_64_ofNat calls _ s "%idxprom332.i" "%sub331.i"
      (by rw [lookupName_cons_self]) hpred32
      [Instr.gep "%arrayidx333.i" (.int 8) (.reg "%cst.i") (.reg "%idxprom332.i"),
       Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")]]
    rw [denoteCode_gep8_ofNat calls _ s "%arrayidx333.i" "%cst.i" "%idxprom332.i"
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact hInv.ptrs.2.2.2.2.1)
      (by rw [lookupName_cons_self]) hpred63
      [Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")]]
    rw [denoteCode_store8_imm calls _ s (BitVec.ofNat 8 1) "%arrayidx333.i"
      (by rw [lookupName_cons_self]) []]
    dsimp only [cells]
    rfl
  have hfind : stage2Body.findBlock s.pc = some walkIf_then330_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_then330_i_find
  have hterm : walkIf_then330_i.term = Term.br "cleanup478.i" := rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump (walkIfThen330OutAt G C s) := by
    simp only [LeanLLVM.step, hfind, hden, hterm, execTerm]
    dsimp only [walkIfThen330OutAt, stateAt]
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-! ### The head's composition above depth zero

The five links `strPath5` composes are depth-independent, so the head's chain to
`if.then219.i` is reused unchanged now that the depth split is `strPath8`'s parameter.
What differs is link 6's edge: `%cmp223.not.i` is `0`, so the run leaves for
`land.lhs.true.i`, and the two marker links follow. -/

/-- The state `if.then219.i` reaches above depth zero: the same three cells as the
depth-zero arm's, with the test's bit `0` and the edge `land.lhs.true.i`. -/
def deep219S (s : State) (rd xv : BitVec 32) : State :=
  { stateAt (cells [("%cmp223.not.i", .int 1 0), ("%call222.i", .int 32 xv),
      ("%26", .int 32 rd)] s.env) s with
    pc := "land.lhs.true.i", pre := some s.pc }

/-- `if.end245.i`'s `%key.1.i` `phi` takes `imm 1` on the `land.lhs.true.i` edge. -/
theorem if_end245_key_land :
    phiIncoming "land.lhs.true.i"
      [("if.then231.i", (Operand.reg "%or.cond.i")),
       ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
       ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] =
      some (.imm (.int 1 (BitVec.ofNat 1 0))) := by
  decide

/-- `if.end245.i`'s `%key.1.i` `phi` takes `%or.cond.i` on the `if.then231.i` edge. -/
theorem if_end245_key_kind :
    phiIncoming "if.then231.i"
      [("if.then231.i", (Operand.reg "%or.cond.i")),
       ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
       ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] =
      some (.reg "%or.cond.i") := by
  decide

/-- **The positive-depth opener's refusal, from `if.end245.i`'s state.**  The nest's own
test is the key bit selected against the callee's answer, so a clear key with a refusing
answer leaves `if.end245.i` for `if.then249.i`, whose offset store and the copy are the
refusal arm.  Two links, and the refusal's witness is the tree's ordinary one: the
segment, the word the copy loads (`refuseSegment_word_of_store`) and the price inside the
entry's credit (`refusePrice_of_le`).

The intermediate state is not spelled: the second link's hypotheses are the first link's
own invariant — `idx_reg` for the index, `regs` for `%e` — which is where the carry's
fields already live. -/
theorem stringDeepRefuse_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.end245.i")
    {p : String} {op : Operand} {k : BitVec 1} {x : BitVec 32}
    (hpre : s.pre = some p)
    (hin : phiIncoming p
      [("if.then231.i", (Operand.reg "%or.cond.i")),
       ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
       ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] = some op)
    (hv : evalOperand s op = some (.int 1 k))
    (hcall : lookupName s.env "%call222.i" = some (.int 32 x))
    (hk0 : k = 0) (hx0 : evalICmp .ne x (BitVec.ofNat 32 0) = 0)
    (hkn : C.k < G.nep) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  have hbit : (if k = 1 then (1 : BitVec 1) else evalICmp .ne x (BitVec.ofNat 32 0))
      = 0 := by
    rw [hk0, hx0]
    rfl
  obtain ⟨s₁, hl₁, _hs₁⟩ :=
    WalkLink.if_end245_i (calls := stage2Calls stage2SubCalls) (G := G) (C := C) (s := s)
      hInv hblock hpre hin hv hcall
  have hcarry₁ : ({ C with block := (if (if k = 1 then (1 : BitVec 1)
      else evalICmp .ne x (BitVec.ofNat 32 0)) = 1 then "if.end256.i"
      else "if.then249.i") } : WalkCarry G) = { C with block := "if.then249.i" } := by
    rw [hbit]
    rfl
  -- the second link's hypotheses are the first link's own invariant
  have hidx : evalOperand s₁ (.reg "%idxprom.i")
      = some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) :=
    LeanLLVM.evalOperand_reg_of hl₁.inv'.idx_reg
  have he : lookupName s₁.env "%e" = some (.ptr C.stage.e) :=
    hl₁.inv'.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.if_then249_i_at (calls := stage2Calls stage2SubCalls) G
      { C with block := "if.then249.i" } s₁ (hcarry₁ ▸ hl₁.inv') rfl
      (j := entryPos G C.k) hidx he
      (le_of_lt (entryPos_lt G hkn))
      (by have := entryPos_lt G hkn; have := WalkGeom.n_lt G; omega)
  have hread : readBytes s₂.mem (C.stage.e + 8) 8 =
      some (wordBytes 8 (entryPos G C.k)) := by
    rw [hs₂]
    simpa only [State.bind] using
      refuseSegment_word_of_store (m := _) (e := C.stage.e) (v := entryPos G C.k)
  exact ⟨_, _, 2, ⟨(Seg.tail (hcarry₁ ▸ hl₁) (Seg.tail hl₂ (Seg.nil hl₂.inv'))).measure,
      rfl, ⟨entryPos G C.k, le_of_lt (entryPos_lt G hkn), hread⟩⟩,
    hl₂.inv'.eoff_le,
    refusePrice_of_le G C (by omega) hkn⟩

/-! ### The arm's class, and its producers

The class's two statements are the byte (`%8 = 34`, which `cont_reg8` reads off the
invariant) and the depth's positivity; the two stack bytes are the carry's maps at
`%sp - 1`, read by witness.  The value-position staging is the **caller's**, at the
state's own root word: the slot is the memory's, so nothing in the invariant names it, and
`HcontOpenCall` is the row that carries the read and the staging.  So the arm's own rows
are the callee's answer, the route and the index. -/

/-- **The positive-depth opener's merge arm, from the staging.**  `HcontArm`'s
`stringOpenAboveZeroMerge` at every state that carries the invariant, the byte `34` and a
positive depth: the byte is the invariant's `%8` cell at the class's value and the two
stack bytes are the carry's maps at `%sp - 1`.  The value-position staging is the
caller's, at the state's own root word `rdv` — the slot is the memory's, so no clause
pins it (`HcontOpenCall` carries the read and the staging).  What the arm still takes
is its route's row: the counted segment, the merge's predecessor and the index, exactly
as the residual table lists them. -/
def hcontArm_stringOpenAboveZeroMerge_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) (hsp : C.sp ≠ 0)
    {rdv : BitVec 32}
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (nepv : BitVec 64)
    (hseg : WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
    (hblock : Cd.block = "cleanup478.i") (hkC : Cd.k = C.k)
    (prev : String) (hprev : prev = "if.then330.i" ∨ prev = "if.else334.i")
    (hpre : sd.pre = some prev)
    (hinc : lookupName sd.env "%inc208.i" = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
    (hadvance : C.k < k2) (hcap : k2 ≤ nepv.toNat)
    (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .stringOpenAboveZeroMerge
    (by rw [← eq_bit_value hclass]; exact cont_reg8 hInv)
    hsp rfl rfl hpreV r hcall
    Cd sd p k2 nepv hseg hblock hkC prev hprev hpre hinc hnepv hadvance hcap hprice

/-- **The positive-depth opener's ready dispatch.**  The arm above through
`HcontArm.dispatch`: the outcome is the merge, at the arm's own count and price. -/
theorem walkDispatch_at_stringOpenAboveZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) (hsp : C.sp ≠ 0)
    {rdv : BitVec 32}
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (nepv : BitVec 64)
    (hseg : WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
    (hblockD : Cd.block = "cleanup478.i") (hkC : Cd.k = C.k)
    (prev : String) (hprev : prev = "if.then330.i" ∨ prev = "if.else334.i")
    (hpre : sd.pre = some prev)
    (hinc : lookupName sd.env "%inc208.i" = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
    (hadvance : C.k < k2) (hcap : k2 ≤ nepv.toNat)
    (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_stringOpenAboveZeroMerge_of_staging C s hInv hclass hsp hpreV r hcall
      Cd sd p k2 nepv hseg hblockD hkC prev hprev hpre hinc hnepv hadvance hcap hprice)

/-- **The positive-depth opener's refusal arm, from the staging.**  The class's own
facts, and the route's witness: `stringDeepRefuse_at` produces it from `if.end245.i`'s
state, and this is where it enters the census. -/
def hcontArm_stringOpenAboveZeroRefuse_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) (hsp : C.sp ≠ 0)
    {rdv : BitVec 32}
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (href : WalkRefuseAt (stage2Calls stage2SubCalls) G C s) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .stringOpenAboveZeroRefuse
    (by rw [← eq_bit_value hclass]; exact cont_reg8 hInv)
    hsp rfl rfl hpreV r hcall href

/-- **The positive-depth opener's refusal dispatch.** -/
theorem walkDispatch_at_stringOpenAboveZeroRefuse_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) (hsp : C.sp ≠ 0)
    {rdv : BitVec 32}
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (href : WalkRefuseAt (stage2Calls stage2SubCalls) G C s) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_stringOpenAboveZeroRefuse_of_staging hInv hclass hsp hpreV r hcall href)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkLandLhsTrue_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen231_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen330_at
#print axioms LeanLLVM.Refinement.WalkScope.stringDeepRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_stringOpenAboveZeroMerge_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_stringOpenAboveZeroRefuse_of_staging

end WalkScope
end LeanLLVM.Refinement
