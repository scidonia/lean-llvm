/-
The letters route: the default arm's span below `if.else387.i`, and its merge.

## The class, as the emitted switch computes it

`if.end372.i`'s tag test is `(%8 == 45) || ((%8 + 208) u< 10)` — the minus sign and the
digits.  Its clear arm sends the walk to `if.else387.i`, and the next three pivots on the
same byte `%8` (`NodeBlock62`: `slt %8, 110`; `NodeBlock60`: `slt %8, 116`;
`LeafBlock58`/`LeafBlock56`/`LeafBlock54`: `eq %8, 116`/`110`/`102`) pick the token's
*kind*.  This module's class is the first pivot's *true* arm and the leaf's clear arm:

```text
slt %8, 110 = 1        %8 < 110 in the signed order (a letter, or a high byte)
eq  %8, 102 = 0        not 'f', so LeafBlock54's else arm
if.else387.i → NodeBlock62 → LeafBlock54 → if.else405.i → if.then413.i     (4 links)
```

which is `LastEntryArm.supplied`'s named route.  The four links are `this module`'s
`lettersSpan`, and their target's `%kind404.i` is `0` — `if.else405.i`'s row of
`if.then413.i`'s `%.sink372` table — which is why the tail that follows is the empty-arm
tail `consumerTailSegAt` composes at kind `0`.

**The two byte classes this route holds, and the one it does not.**  `slt` is signed, so
`slt %8, 110 = 1` holds for `0 … 109` and for `128 … 255`: the letters and the high bytes.
It does not hold for `110 … 127`, which is why the bytes `126` and `127` are *not* this
class — they take the longer `NodeBlock60 → LeafBlock58` span that `walkHeadChainCSeg`
composes, and are `HcontArm.ws`/`.cleanup`'s.  The byte `102` (`'f'`) satisfies the first
pivot and takes `LeafBlock54`'s *true* arm (`if.then397.i`, kind `9`); it is the one byte of
the class this module does not describe, and it is what `.supplied` still carries.

## What the route's composition is, and what it costs

Above `if.else387.i` the head's four pivots select **different blocks per byte class** (`'a'`
at `97` takes `NodeBlock19 → NodeBlock11 → LeafBlock9`; `200` takes `NodeBlock5 →
LeafBlock`), so the chain from the loop head to this span is the class's own and is not one
composition.  It enters here as a counted segment at its own count, the way the tail's
three calls do elsewhere, and the count this module composes is the one it can see:

| piece | source | links |
|---|---|---|
| the head's chain to `if.else387.i`, and the count test, the bound, the whitespace check and the run | the arm's own segment, at `12` | `12` |
| `lettersSpan` (this module) | `headChain_else387_at`, `NodeBlock62_at`, `LeafBlock54_at`, `headChain_else405_at` | `4` |
| the tail's three calls on their empty arm | the arm's own segment, at `3` | `3` |
| the merge `walkIfEnd473_at` | this module | `1` |

`12 + 4 + 3 + 1 = 20`, and the price is `20 + 2 = 22 ≤ 32·Δk` at `Δk = 1` — inside the
entry allowance with ten links to spare, and with **no byte term**: this arm's scan is
empty, because the token ends where the entry does.  At the last entry the same composition
runs at **eleven** head links (`19 + 2 = 21 ≤ 32`): the count test fails there, so
`sw.default.i → cond.end349.i` replaces `sw.default.i → cond.true345.i → cond.end349.i`.

## The scan, and which hypothesis it contributes

Where the byte before the entry's end is whitespace the walk runs that run first and the
token's end `%ee.1.i` is the run's *stop* `k`, not the entry's end; the extra-token scan
then traverses `[k, v)` and `walkScanToMerge` is the induction over its visits.  Its
hypotheses are the traversal's: `hbyte` (every index the scan visits has a whitespace byte),
`hguard` (the latch's measure) and the round, and `walkScanArrival457` is the induction that
composes them at `n ≤ stage2ByteAllowance * (c - 1 - i)` visits.

Both arms this module's composition backs — `HcontArm.letters` and `LastEntryArm.letters` —
are the **scan-free** class: `%35` is not whitespace, so the token's end is the entry's end
(the seam's `%ee.1.i` is `%cond350.i` on the whitespace check's else arms) and the copy
call's test `ult %ee.1.i %cond350.i` is `ult v v`, i.e. false.  So the scan contributes
*nothing* to this arm's segment, and the class whose scan runs is `HcontFacts`'s — `.ws`'s,
whose segment is `walkRevolutionMergeSegWs` and whose induction is `scanWsRounds`'s (the
visit form at `4` steps) and the bundle's `walkScanToMerge`.
-/
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The span's carries

`if.else387.i`'s target is `HeadC₆₂` (`JsonStage2WalkHeadChainC`); the leaves below it are
this route's own, so their carries are named here.  The last one is `HeadC₄₁₃`'s nest
applied to the leaf's carry, so the span's target carry is the one `walkHeadChainC` also
uses at its own end — both routes enter `if.then413.i` and the carry is a block name. -/

/-- `LeafBlock54`'s carry: `%8 < 110` in the signed order. -/
abbrev LetC₅₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadC₆₂ C with block := "LeafBlock54" }

/-- `if.else405.i`'s carry: the leaf's clear arm. -/
abbrev LetC₄₀₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { LetC₅₄ C with block := "if.else405.i" }

/-- `LeafBlock54`'s target: `%Pivot63`'s bite on the arm below `110`. -/
def LetS54 (s : State) (x : BitVec 8) : State :=
  { ((HeadS62 s).bind "%Pivot63" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 110)))) with
    pc := "LeafBlock54", pre := some (HeadS62 s).pc }

/-- `if.else405.i`'s target: `%SwitchLeaf55`'s bite on the leaf's clear arm. -/
def LetS405 (s : State) (x : BitVec 8) : State :=
  { ((LetS54 s x).bind "%SwitchLeaf55" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 102)))) with
    pc := "if.else405.i", pre := some (LetS54 s x).pc }

/-- The span's target: `if.else405.i`'s empty body, at `if.then413.i`. -/
def LetS413 (s : State) (x : BitVec 8) : State :=
  { LetS405 s x with pc := "if.then413.i", pre := some (LetS405 s x).pc }

/-! ### The `%8` cells the pivots read

Neither pivot binds `%8`, so the byte at each of them is the one the span's entry read. -/

/-- `%8` at `LeafBlock54` is the span's entry's: `NodeBlock62` binds `%Pivot63` only. -/
theorem LetS54_env8 (s : State) (x : BitVec 8)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    evalOperand (LetS54 s x) (.reg "%8") = some (.int 8 x) := by
  simp only [LetS54, HeadS62, State.bind, evalOperand,
    lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
  exact h8

/-- `%8` at `if.else405.i` is the span's entry's, for the same reason. -/
theorem LetS405_env8 (s : State) (x : BitVec 8)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    evalOperand (LetS405 s x) (.reg "%8") = some (.int 8 x) := by
  simp only [LetS405, LetS54, HeadS62, State.bind, evalOperand,
    lookupName_cons_ne (k := "%SwitchLeaf55") (n := "%8") _ _ (by decide),
    lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
  exact h8

/-- **The letters span**: `if.else387.i`'s entry to `if.then413.i` in four links, on the
byte class `slt %8, 110 = 1` and `%8 ≠ 102`.

The first link is the empty body's (`headChain_else387_at`), the second
`NodeBlock62`'s pivot, the third `LeafBlock54`'s leaf test — both named at their own
states — and the fourth `if.else405.i`'s empty body.  The successor the layer states
existentially in the first and fourth links is `HeadS62`/`headChain_else405_at`'s own
target, which is what makes the composition stitched at names. -/
theorem lettersSpan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0) :
    Seg calls G C s (HeadC₄₁₃ (LetC₄₀₅ C)) (LetS413 s x) 4 := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x) := h8
  -- 2. `NodeBlock62`, whose bit is set
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "LeafBlock54" from by rw [h110]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = LetS54 s x := hs₂
  rw [hs₂'] at hl₂
  -- 3. `LeafBlock54`, whose equality test is clear
  have h8₂ : evalOperand (LetS54 s x) (.reg "%8") = some (.int 8 x) :=
    LetS54_env8 s x h8
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.LeafBlock54_at (calls := calls) (G := G)
    (C := LetC₅₄ C) (s := LetS54 s x) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .eq x (BitVec.ofNat 8 102) = 1 then "if.then397.i"
    else "if.else405.i") = "if.else405.i" from by rw [hne102]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = LetS405 s x := hs₃
  rw [hs₃'] at hl₃
  -- 4. the empty body at `if.else405.i`
  obtain ⟨s₄, hl₄, hs₄⟩ := headChain_else405_at (calls := calls) G (LetC₄₀₅ C)
    (LetS405 s x) hl₃.inv' rfl
  have hs₄' : s₄ = LetS413 s x := hs₄
  rw [hs₄'] at hl₄
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄
    (Seg.nil hl₄.inv'))))

/-! ### The route's composition to the merge

The span, the tail's three calls on their empty arm, and the merge's own step.  The two
segments above the span and below it enter at their own counts — the head's at `12` (its
four pivots, `sw.default.i`'s succeeding arm, `cond.true345.i`, the bound's `phi`, the
whitespace check's four and the seam's one), the tail's at `3` — because the head's four
pivots pick different blocks per byte class and the tail's three calls are their own
callees' contracts.  What this module composes is what it can see: `4 + 1`, and the
twenty the whole route costs.

The merge's three cells are read at the segment's own endpoint: `%inc.i` and `%nep` are
`WalkInv` clauses at the tail's target (`inc_reg`, `regs`), the tail's carry keeps the
head's index (`hkt`), and the merge's block binds no cell, so the endpoint's environment
is the tail's end's. -/
theorem lettersCleanupMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok))
    (hnH : nH ≤ 12) (hΔ : C.k + 1 - C.k = 1) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      Cd.k = C.k ∧
      sd.pre = some "if.end473.i" ∧
      lookupName sd.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      p + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) +
        stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  -- the span, from the head segment's endpoint
  have hspan : Seg (stage2Calls stage2SubCalls) G Cm sm
      (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm x) 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hHead.inv' hm (h8m) h110 hne102
  -- the head's count and the span's four, then the tail's three
  have hsegH : WalkSegment (stage2Calls stage2SubCalls) G C s
      (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm x) (nH + 4) :=
    hHead.trans (Seg.measure hspan)
  have hsegT : WalkSegment (stage2Calls stage2SubCalls) G C s Ct st (nH + 4 + 3) :=
    hsegH.trans hTail
  -- the merge's step
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := Ct) (s := st)
      hsegT.inv' ht htok
  rw [hs₂] at hl₂
  -- the cells at the merge
  have hpc : st.pc = "if.end473.i" := by
    rw [← ht]; exact hsegT.inv'.pc_eq
  have hinc : lookupName st.env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [← htk]
    exact hsegT.inv'.inc_reg
  have hnep : lookupName st.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) :=
    hsegT.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  refine ⟨{ Ct with block := "cleanup478.i" },
    { st with pc := "cleanup478.i", pre := some st.pc }, nH + 8,
    hsegT.trans (WalkSegment.of_link hl₂), rfl, htk, ?_, ?_, ?_, ?_⟩
  · -- the merge's predecessor is the tail's end
    show (some st.pc : Option String) = some "if.end473.i"
    rw [hpc]
  · -- `%inc.i` at the merge: the merge binds no cell
    show lookupName st.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
    exact hinc
  · show lookupName st.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))
    exact hnep
  · -- the price: the head's count at its bound, and the entry's own allowance
    have hb : nH + 8 + 2 ≤ 12 + 8 + 2 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one]
    omega

end WalkScope
end LeanLLVM.Refinement
