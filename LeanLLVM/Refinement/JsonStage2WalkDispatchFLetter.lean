/-
The `'f'` leaf: the letters span's true arm, and its merge.

## The class

`if.end372.i`'s tag test clear sends the walk to `if.else387.i`, and the first pivot
`NodeBlock62`'s `slt %8, 110` is *true* — the letters' side of the tree — at the bytes
below `110` in the signed order (and at the high bytes, which are negative there).
`LeafBlock54`'s `eq %8, 102` then picks the token's kind: `102` (`'f'`) takes the leaf's
*true* arm, an empty body to `if.then413.i`, where `%.sink372`'s table gives kind `9`.

```text
slt %8, 110 = 1        %8 < 110 in the signed order
eq  %8, 102 = 1        'f'
if.else387.i → NodeBlock62 → LeafBlock54 → if.then397.i → if.then413.i   (4 links)
```

This is the one byte the letters route (`JsonStage2WalkDispatchLetters`) does not
describe: `lettersSpan` takes `LeafBlock54`'s *else* arm.  The two spans differ in their
third link's successor and in the kind the target records, not in their length.

## The composition, and what it costs

| piece | source | links |
|---|---|---|
| the head's chain to `if.else387.i`, the count test, the bound, the whitespace check and the run | the arm's own segment, at `nH ≤ 12` | `nH` |
| `fSpan` (this module) | `headChain_else387_at`, `NodeBlock62_at`, `LeafBlock54_at`, the `if.then397.i` body | `4` |
| the tail's three calls on their empty arm | the arm's own segment (`hTail`) | `3` |
| the merge `walkIfEnd473_at` | `fCleanupMerge_at` | `1` |

`nH + 8` links, and the price is `nH + 8 + 2 ≤ 32·Δk + 8·ΔA` at `nH ≤ 12`: twenty-two
against the entry allowance's thirty-two, the same total the letters route costs, because
the two spans are both four links.  **No byte term is spent** — the class is the
scan-free one, so the copy call's test is `ult v v` and no visit is entered.

The head chain is the class's own and enters as a counted segment, as it does on the
letters route: `'f'` at `102` takes `NodeBlock19 → NodeBlock11 → LeafBlock9`, a high byte
takes `NodeBlock5 → LeafBlock`, and the two are not one composition.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLetters

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The leaf's true arm, named

`LeafBlock54`'s true arm is the letters route's sibling: the same leaf, the same pivot,
and the other successor.  The carries are the letters module's `LetC₅₄` continued at
`if.then397.i`, and the states are that pivot's own `bind` with the empty body's edge. -/

/-- `LeafBlock54`'s carry on its true arm. -/
abbrev FC₃₉₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { LetC₅₄ C with block := "if.then397.i" }

/-- The arm's target: `if.then397.i`'s empty body, at `if.then413.i`. -/
abbrev FC₄₁₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { FC₃₉₇ C with block := "if.then413.i" }

/-- `LeafBlock54`'s target on its true arm: `%SwitchLeaf55`'s bite, at `if.then397.i`. -/
def FS397 (s : State) (x : BitVec 8) : State :=
  { ((LetS54 s x).bind "%SwitchLeaf55" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 102)))) with
    pc := "if.then397.i", pre := some (LetS54 s x).pc }

/-- The arm's target: `if.then397.i`'s empty body, at `if.then413.i`. -/
def FS413 (s : State) (x : BitVec 8) : State :=
  { FS397 s x with pc := "if.then413.i", pre := some (FS397 s x).pc }

/-- **`if.then397.i`'s target, named.**  An empty body and one `br`, so the target is the
source with the edge's successor and the environment is untouched — the identification
`headChain_else405_at` makes at the leaf's other arm. -/
theorem fChain_then397_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then397.i") :
    ∃ (s' : State), WalkLink calls G C s ({ C with block := "if.then413.i" }) s' ∧
      s' = { s with pc := "if.then413.i", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_then397_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_then397_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_then397_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_then397_i)
    (dest := "if.then413.i") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **The `'f'` span**: `if.else387.i`'s entry to `if.then413.i` in four links, on
`102`'s own byte.

The first link is the empty body's, the second `NodeBlock62`'s pivot on its true arm, the
third `LeafBlock54`'s leaf test on its true arm — both named at their own states — and the
fourth `if.then397.i`'s empty body.  The states are `LetS54`/`FS397`/`FS413`, so a
consumer appends its tail at `if.then413.i` with the target as an index rather than a
witness. -/
theorem fSpan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1) :
    Seg calls G C s (FC₄₁₃ C) (FS413 s x) 4 := by
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
  -- 3. `LeafBlock54`, whose equality test is set
  have h8₂ : evalOperand (LetS54 s x) (.reg "%8") = some (.int 8 x) :=
    LetS54_env8 s x h8
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.LeafBlock54_at (calls := calls) (G := G)
    (C := LetC₅₄ C) (s := LetS54 s x) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .eq x (BitVec.ofNat 8 102) = 1 then "if.then397.i"
    else "if.else405.i") = "if.then397.i" from by rw [h102]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = FS397 s x := hs₃
  rw [hs₃'] at hl₃
  -- 4. the empty body at `if.then397.i`
  obtain ⟨s₄, hl₄, hs₄⟩ := fChain_then397_at (calls := calls) G (FC₃₉₇ C)
    (FS397 s x) hl₃.inv' rfl
  have hs₄' : s₄ = FS413 s x := hs₄
  rw [hs₄'] at hl₄
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄ (Seg.nil hl₄.inv'))))

/-! ### The route's composition to the merge

The span, the tail's three calls on their empty arm, and the merge's own step.  The head
and the tail enter at their own counts, exactly as they do on the letters route: the head's
four pivots pick different blocks per byte class, and the tail's three calls are their own
callees' contracts.  What this module composes is `4 + 1`, and the `nH + 8` the whole
route costs.

The merge's three cells are read at the segment's own endpoint: `%inc.i` and `%nep` are
`WalkInv` clauses there, the tail's carry keeps the head's index (`htk`), and the merge's
block binds no cell, so the endpoint's environment is the tail's end's.
-/
theorem fCleanupMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm x) Ct st 3)
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
      (FC₄₁₃ Cm) (FS413 sm x) 4 :=
    fSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hHead.inv' hm h8m h110 h102
  -- the head's count and the span's four, then the tail's three
  have hsegH : WalkSegment (stage2Calls stage2SubCalls) G C s
      (FC₄₁₃ Cm) (FS413 sm x) (nH + 4) :=
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

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.fChain_then397_at
#print axioms LeanLLVM.Refinement.WalkScope.fSpan
#print axioms LeanLLVM.Refinement.WalkScope.fCleanupMerge_at

end WalkScope
end LeanLLVM.Refinement
