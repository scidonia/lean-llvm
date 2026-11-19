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

**Correction to this module's first report.**  The survey it carried used a word-boundary
pattern that cannot match before `_`, so it listed `if_then432_i`, `if_else43_i`,
`if_end48_i`, `if_end67_i`, `if_then19_i`, `if_then25_i`, `land_rhs71_i` and
`while_end78_i` as absent.  They all exist (`JsonStage2WalkScopeClassC`,
`JsonStage2WalkScopeClassAB`, `JsonStage2WalkEntry`, `JsonStage2WalkFinal`,
`JsonStage2WalkCall`, `JsonStage2WalkPhi`).  The path's links are complete except two
**loop-body** links, and those are not the real obstruction:

* `while_body_i104` — the slow scan's increment (`%inc.i105 = %ee.011.i + 1`), its exit test
  (`%exitcond.not.i`) and its two edges (back to `land.rhs.i103`, out to `cleanup474.i`);
* `while_body76_i` — the escape unit's scan's same shape, on `%exitcond24.not.i`.

Both are two-instruction blocks (`add`, `icmp`) with a `condbr`; `denoteCode_cons_of` plus
`step_add_reg` and `walkDenoteCode_icmp` give the block step, and `callQuietBr` gives the
link, so each is a mechanical addition rather than a modelled gap.

**What is missing is the scan's segment, not its links.**  `ScanVisits`
(`JsonStage2WalkDispatchRunOfStaging`) models the *other* scan — `while.body462.i` at
`land.rhs457.i` — not this one; `while.body.i104`'s loop has no visit model, no induction
and no segment from `land.rhs.i103` to either exit (`while.end.i` on a whitespace byte, or
`cleanup474.i` when the counter reaches `%cond.i`).  Such a segment is parametric in the
number of visited bytes `G.bs[entryPos … %cond.i)` and must be priced by that number, in the
shape `runLast_price_with_credit` gives the merge endpoint (`8·(G.n − entryPos G C.k)`
for the byte term); the constant bound `refusePrice_of_le` is not applicable, as the
instruction says.

**The class's own path is narrower than the list.**  At `%8 ∈ {126, 127}`, `%cmp343.i` is
`ult %inc.i %nep` with `%inc.i = C.k + 1 = G.nep`, so it is `0` and `if.then432.i` takes
`cond.end.i96` with `%cond.i = %4 = G.n`; `%cmp310.i` is `ugt G.n (entryPos G C.k)`, i.e.
`1`, so the scan is entered.  Its two exits then reach `cleanup474.i` directly (counter at
the bound, `%cmp6.i`) or, on a whitespace stop, `if.end.i97` whose tag test on
`%41 = %8 = 126/127` is clear, then `if.else.i` → `NodeBlock83` → `NodeBlock81` →
`LeafBlock79` → `if.else43.i` → `cleanup474.i`.  So `if.end48.i`, `if.end67.critedge.i`,
`if.end67.i`, `if.then19.i`, `if.then25.i`, `land.rhs71.i`, `while.body76.i` and
`while.end78.i` are on *other* literals' paths (the numeral arm and the escape unit), not
on this class's; their presence is needed for a general `badToken` route, not for
`HlastSeam.answerOneRefuse`'s inhabitant.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamRow
import LeanLLVM.Refinement.JsonStage2WalkDispatchSlowRound
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
#print axioms LeanLLVM.Refinement.WalkScope.hlastAnswerZeroRefuse
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeamAnswerZero_nonempty
#print axioms LeanLLVM.Refinement.WalkScope.hlastAnswerZeroRefuse


/-! ### The answer-`1` arm's refusal route

`HlastSeam.answerOneRefuse`'s arm reaches the copy through the error path: the seam's
three links (`if.then413.i`, `if.then425.i_refuse`, `if.then432.i`), the bound `phi` at
`cond.end.i96`, the slow scan's round (`slowRun`) to `cleanup474.i` and the release.  The
class's prefix to the scan's landing is `hlastTailSegByte` plus those four links; the
round is the scan's own segment, so the route is the prefix composed with it. -/

/-- **The answer-`1` refusal route, at the head.**  The prefix is the class's (the tail
begins at `if.then413.i` and the seam's three links and the bound `phi` place the scan's
landing), and the scan's segment is `slowRun`'s. -/
noncomputable def hlastAnswerOneRefuseRoute {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {C1 : WalkCarry G} {s1 : State} {n1 k : Nat}
    (hprefix : WalkSegment (stage2Calls stage2SubCalls) G C s C1 s1 n1)
    (hn1 : n1 ≤ 20)
    (hblock1 : C1.block = "land.rhs.i103") (hInv1 : WalkInv G C1 s1)
    (hpre1 : s1.pre = some "cond.end.i96")
    (hcnt1 : evalOperand s1 (slowOp (some "cond.end.i96"))
      = some (.int 64 (BitVec.ofNat 64 (entryPos G C1.k))))
    (hcond1 : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 G.n)))
    (hqn : entryPos G C1.k < G.n)
    (hbit : (evalICmp .eq (BitVec.ofNat 8 (G.bs.getD (entryPos G C1.k) 0).toNat)
      (BitVec.ofNat 8 45) ||| evalICmp .ult
        (BitVec.ofNat 8 (G.bs.getD (entryPos G C1.k) 0).toNat + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD (entryPos G C1.k) 0).toNat)
      (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD (entryPos G C1.k) 0).toNat)
      (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq (BitVec.ofNat 8 (G.bs.getD (entryPos G C1.k) 0).toNat)
      (BitVec.ofNat 8 116) = 0)
    (halen : C1.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C1.evlen ≤ G.evcap)
    (hword1 : readBytes s1.mem (C1.stage.e + 8) 8 = some (wordBytes 8 k)) (hk : k ≤ G.n)
    (heoff1 : C1.eoff ≤ G.n)
    (hinner : G.n - entryPos G C1.k ≤ C1.inner)
    (hΔ : 1 ≤ G.n - entryPos G C1.k)
    (hklt : C1.k < G.nep) (hkC : C1.k = C.k) :
    HlastRefuseRoute G C s := by
  let h := slowRun G C1 s1 k hInv1 hblock1 hpre1 hcnt1 hcond1 hqn hbit h110 h116 h116eq
    halen hevlen hword1 hk heoff1 hinner
  let Cd : WalkCarry G := Classical.choose h
  let h1 := Classical.choose_spec h
  let sd : State := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let n : Nat := Classical.choose h2
  let h3 := Classical.choose_spec h2
  exact ⟨Cd, sd, n1 + n, hprefix.trans h3.1, h3.2.1, Classical.choose h3.2.2.2.1,
    (Classical.choose_spec h3.2.2.2.1).1,
    (Classical.choose_spec h3.2.2.2.1).2,
    h3.2.2.2.2, by rw [← hkC]; exact slowAnswerOnePrice G C1 hn1 h3.2.2.1 hΔ hklt⟩

/-- **The answer-`1` arm is inhabited**, its route being the class's: the seam's refusal
rows and the priced route to the copy. -/
theorem hlastSeamAnswerOne_nonempty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (rows : HlastSeamRefusal G C s) (_route : HlastRefuseRoute G C s) :
    Nonempty (HlastSeam G C s) :=
  ⟨HlastSeam.answerOneRefuse rows⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hlastAnswerOneRefuseRoute
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeamAnswerOne_nonempty

end WalkScope
end LeanLLVM.Refinement
