/-
# The last level's answer-`0` refusal route

`HlastSeam.answerZero` (`JsonStage2WalkDispatchSeams`) names the arm `s2_value_pos` takes
when its answer is `0`: `if.then413.i`'s zero branch to `if.then418.i` (the refusal word at
`%e + 8`), `cleanup474.i`'s release, and the copy at `if.then`.  No scalar call is made.

This module composes those three links into one priced route.  The first is
`WalkLink.if_then413_i` at the seam's state (the kind store, the root-slot load, the call
and its zero branch), the second `WalkLink.if_then418_i_at` (the named store target), and
the third `WalkLink.cleanup474_i`, whose target this module names too (`cleanup474_i_at`,
because the release is what carries the stored refusal word to the copy).  The result is a
`WalkSegment … 3` ending at `if.then`, the word the copy's `%off` load reads, and — with the
class's own prefix segment to the tail start — a `WalkDispatchResult.refuse` at the head.

The count is why this arm is pricable where the answer-`1` arm is not: three links at the
seam plus the class prefix (`12 + hlastByteCount hb ≤ 16`) is at most nineteen, and
`refusePrice_of_le` spends the entry's own thirty-two.

## What the answer-`1` arm's continuation still lacks

`HlastSeam.answerOneRefuse`'s route is `HlastRefuseRoute` with the error path after
`if.then425.i`: `if.then432.i` → the scan/escape tree → `cleanup474.i` → `if.then`.  Its
statement does not change here; what it needs is links the tree does not have, and this is
the exact list (checked against `WalkLink`'s declarations):

* **no link at all** for `if.then432.i` itself (the `%cmp343.i` branch), `while.body.i104`
  (the scan's increment and exit test), `if.end48.i`, `if.end67.criticiedge.i`/`if.end67.i`,
  `if.then19.i` (the numeral arm: two `lifetime.start`s and the `num_fast_el1` call),
  `if.then25.i`, `if.else43.i`, and the escape unit's own scan
  (`land.rhs71.i`, `while.body76.i`, `while.end78.i`);
* **present**: `cond.true.i106`, `cond.end.i96`, `land.rhs.i103`, `NodeBlock73`,
  `NodeBlock71`, `LeafBlock64`/`67`/`69`, `while.end.i`, `if.end.i97`, `if.else.i`,
  `NodeBlock83`/`81`, `LeafBlock75`/`77`/`79`, and `cleanup474.i`;
* **the price**: the scan's length is the entry's own token, so the count is not the
  constant `refusePrice_of_le` bounds — it must be charged per byte against
  `8·(G.n − entryPos G C.k)`, which is the accounting `RunLastFacts`/`runLast_price_with_credit`
  make for the merge endpoint and no segment makes for `if.then`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamRow
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchZeroOfStaging
import LeanLLVM.Refinement.JsonStage2WalkScopeClassC
import LeanLLVM.Refinement.JsonStage2WalkCall

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **`cleanup474.i`'s target, named**: the release is a `lifetime.end` and a branch, so
its target is the source's memory at the copy's block. -/
theorem cleanup474_i_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup474.i")
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "if.then" } s' ∧
      s' = { stateAt s.env s with pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.cleanup474_i G C s hInv hblock htok
  refine ⟨s', hl, ?_⟩
  have hpc : s.pc = C.block := hInv.pc_eq
  have hden : denoteCode (stage2Calls stage2SubCalls)
      [Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
         (Ty.ptr, Operand.reg "%t352.i")]] s = some (stateAt s.env s) := by
    change denoteCode (stage2Calls stage2SubCalls)
      [Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
         (Ty.ptr, Operand.reg "%t352.i")]] (stateAt s.env s) = some (stateAt s.env s)
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 24) (obj := "%t352.i") htok ([] : List Instr)]
    rfl
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s =
      Ctrl.jump { stateAt s.env s with pc := "if.then", pre := some s.pc } := by
    simp only [LeanLLVM.step, hpc, hblock, walkCleanup474_find, hden, walkCleanup474,
      execTerm]
    have hpc' : (stateAt s.env s).pc = "cleanup474.i" := by
      show s.pc = "cleanup474.i"
      rw [hpc, hblock]
    rw [hpc']
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-! ### The three links, from a state at `if.then413.i`

The seam's state is the one the class's prefix reaches; the answer is the value-position
call's word and the branch is its zero arm.  The remaining cells (`%kind404.i`,
`%root_done.i`) are the head's, and the position word is the invariant's `idx_reg`. -/

/-- **The answer-`0` route**, at any state at `if.then413.i`: the zero branch, the refusal
store and the release, as one three-link segment to the copy. -/
theorem hlastAnswerZeroRoute {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then413.i")
    {p : String} (hpre : s.pre = some p)
    {op : Operand} {cA rdv x : BitVec 32}
    (hphi : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 32 cA))
    (hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next)
    (hx : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next = some r →
      r.ret = .int 32 x)
    (hx0 : evalICmp .eq x (BitVec.ofNat 32 0) = 1) :
    ∃ (Cd : WalkCarry G) (sd : State), Cd.block = "if.then" ∧
      Cd.eoff = entryPos G C.k ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 3 ∧
      readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 (entryPos G C.k)) := by
  -- 1. the kind store, the root-slot load, the call and its zero branch
  obtain ⟨s₁, hl₁⟩ := WalkLink.if_then413_i (reg := "%.sink372") (G := G) (C := C) (s := s)
    hInv hblock hpre hphi hop hkind hrd hread hpreV hx
  have hb₁ : (if evalICmp .eq x (BitVec.ofNat 32 0) = 1 then "if.then418.i"
      else "if.then425.i") = "if.then418.i" := by
    rw [hx0]; rfl
  rw [hb₁] at hl₁
  -- 2. the refusal store at the entry's position
  have hIdx : lookupName s₁.env "%idxprom.i" =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) :=
    hl₁.inv'.idx_reg
  have hv : evalOperand s₁ (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) :=
    LeanLLVM.evalOperand_reg_of hIdx
  have he : lookupName s₁.env "%e" = some (.ptr C.stage.e) :=
    hl₁.inv'.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.if_then418_i_at (calls := stage2Calls stage2SubCalls) (G := G) _ s₁
      hl₁.inv' rfl hv he
      (entryPos_le G C.k) (entryPos_lt_64 G C.k)
  -- 3. the release: the token record's lifetime end
  have htok : lookupName s₂.env "%t352.i" = some (.ptr C.stage.tok) :=
    hl₂.inv'.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  obtain ⟨s₃, hl₃, hs₃⟩ := cleanup474_i_at (G := G) _ s₂ hl₂.inv' rfl htok
  -- the composed endpoint carry
  let Cd : WalkCarry G :=
    { C with block := "if.then", eoff := entryPos G C.k, refusal := true }
  refine ⟨Cd, s₃, rfl, rfl, ?_, ?_⟩
  · exact (WalkSegment.of_link hl₁).trans
      ((WalkSegment.of_link hl₂).trans (WalkSegment.of_link hl₃))
  · -- the refusal word, written at the store and carried across the release
    rw [hs₃, hs₂]
    simp only [stateAt]
    exact refuseSegment_word_of_store (m := s₁.mem) (e := C.stage.e)
      (v := entryPos G C.k)

/-! ### The seam's zero row, from the route

The route above is the `answerZero` arm's segment.  The row also carries the first call's
facts (`HlastSeamZero`), so the producer takes those and the route's own existentials. -/

/-- **The zero row's route as a `HlastRefuseRoute`**, with the credit it needs stated: the
three links cost `5` and the entry's own allowance pays for them. -/
noncomputable def hlastAnswerZeroRefuseRoute {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State)
    (hroute : ∃ (Cd : WalkCarry G) (sd : State), Cd.block = "if.then" ∧
      Cd.eoff = entryPos G C.k ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 3 ∧
      readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 (entryPos G C.k)))
    (hcredit : 3 + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k)) :
    HlastRefuseRoute G C s := by
  classical
  let Cd : WalkCarry G := Classical.choose hroute
  let sd : State := Classical.choose (Classical.choose_spec hroute)
  let rest := Classical.choose_spec (Classical.choose_spec hroute)
  exact ⟨Cd, sd, 3, rest.2.2.1, rest.1, entryPos G C.k, entryPos_le G C.k, rest.2.2.2,
    (by rw [rest.2.1]; exact entryPos_le G C.k), hcredit⟩

/-- **The answer-`0` arm is inhabited**: `HlastSeam.answerZero`, with the segment the
producer composed. -/
theorem hlastSeamAnswerZero_nonempty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (rows : HlastSeamZero G C s) : Nonempty (HlastSeam G C s) :=
  ⟨HlastSeam.answerZero rows⟩

/-! ### From the head: the prefix and the route

`hlastTailSegByte` (`JsonStage2WalkPrefixCount`) is the class's prefix to the tail start;
the route above is the seam's.  Composed, they are a refusal at the head, and the price is
the entry's own (`refusePrice_of_le`: at most thirty steps fit `32·Δk`). -/

/-- **The answer-`0` refusal, at the head.**  The prefix is the class's own (produced by
`hlastTailSegByte`); the route is the seam's.  The result is
`WalkDispatchResult.refuse` at `if.then`. -/
theorem hlastAnswerZeroRefuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {x : BitVec 8} {inc nep : BitVec 64} {v : Nat} {ix : BitVec 64} {b35 : UInt8}
    (hb : HcontByteRoute (head35 b35))
    (hprefix : WalkSegment (stage2Calls stage2SubCalls) G C s (TailStartC C)
      (hlastTailByte C s x inc nep v ix b35 hb) (12 + hlastByteCount hb))
    (route : HlastRefuseRoute G (TailStartC C) (hlastTailByte C s x inc nep v ix b35 hb))
    (hsmall : 12 + hlastByteCount hb + route.n ≤ 30)
    (hk : C.k < G.nep) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  WalkDispatchResult.refuse route.Cd route.sd (12 + hlastByteCount hb + route.n)
    (hprefix.trans route.seg) route.hblock ⟨route.k, route.hk, route.hword⟩ route.herr
    (by
      have h := refusePrice_of_le G C hsmall hk
      simpa only [Nat.add_assoc] using h)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cleanup474_i_at
#print axioms LeanLLVM.Refinement.WalkScope.hlastAnswerZeroRoute
#print axioms LeanLLVM.Refinement.WalkScope.hlastAnswerZeroRefuseRoute
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeamAnswerZero_nonempty
#print axioms LeanLLVM.Refinement.WalkScope.hlastAnswerZeroRefuse

end WalkScope
end LeanLLVM.Refinement
