/-
The class-C span's leaves: `LeafBlock56`'s two arms, `LeafBlock58`'s true arm, and the
merge the four share.

## The tree, below the seam

`if.end372.i`'s tag test clear sends the walk to `if.else387.i`, and the four pivots on
`%8` below it are a comparison tree whose leaves pick the *kind* the token records:

```text
if.else387.i → NodeBlock62   slt %8, 110
             → NodeBlock60   slt %8, 116
             → LeafBlock58   eq  %8, 116      true → if.then413.i     (kind 8)
             → LeafBlock56   eq  %8, 110      true → if.then403.i     (kind 10)
             → LeafBlock54   eq  %8, 102      true → if.then397.i     (kind 9)
                                              clear → if.else405.i    (kind 0)
```

`LeafBlock54`'s true arm is `JsonStage2WalkDispatchFLetter`'s, and both of its arms are
the letters span's.  What this module composes is the other two leaves' arms, at the bytes
they select:

| bytes | route below `if.else387.i` | links | kind |
|---|---|---|---|
| `110` | `NodeBlock62`(clear) `NodeBlock60`(set) `LeafBlock56`(eq set) `if.then403.i` | `5` | `10` |
| `111 … 115` | the same three, `LeafBlock56`'s eq clear, `if.else405.i` | `5` | `0` |
| `116` | `NodeBlock62`(clear) `NodeBlock60`(clear) `LeafBlock58`(eq set) | `4` | `8` |
| `117 … 125` | the same three, `LeafBlock58`'s eq clear, `if.else405.i` | `5` | `0` |

The last row is `walkHeadChainCSeg`'s, composed in `JsonStage2WalkPrefixCount`; the other
three are this module's.  `126`/`127` take the last row's route and are `HcontArm.ws`/
`.cleanup`'s class, which is why the class here stops at `125`.

## Why one span theorem per leaf arm, and one merge

Each leaf arm's target is a different leaf block's `bind`, so each span is stated at its
own endpoint — `if.then403.i`'s and `if.else405.i`'s empty bodies are different blocks, and
`LeafBlock58`'s true arm reaches `if.then413.i` without an empty body between.  The
**merge** is the same for all four: the tail's three calls and `walkIfEnd473_at` read only
the endpoint's invariant, its block name and its `%t352.i` cell, so one theorem
(`classCMerge_at`) composes them given the span as a segment at `nS ≤ 5`.

## The counts and the price

`nH + nS + 3 + 1` links, at `nH ≤ 12` and `nS ≤ 5`: twenty-three plus two against the
entry allowance's thirty-two, and the byte term is the contract's rather than spent — the
tail ends at `if.end473.i`, so the copy call's test is `ult v v` and no visit is entered.
The class is the scan-free one on all four rows; the same four routes with a run are
`.run`'s.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchFLetter

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The carries

`HeadS60` (the first pivot's clear arm) and `HeadS58` (the second's clear arm) are
`JsonStage2WalkHeadChainC`'s; the leaf below them is this module's, and so is the state
the leaf's own `bind` leaves. -/

/-- The carry at `LeafBlock56`: the second pivot's *set* arm. -/
abbrev ClsC₅₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadC₆₀ C with block := "LeafBlock56" }

/-- The carry at `LeafBlock56`'s true arm. -/
abbrev ClsC₄₀₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ClsC₅₆ C with block := "if.then403.i" }

/-- The carry at `LeafBlock56`'s else arm. -/
abbrev ClsC₄₀₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ClsC₅₆ C with block := "if.else405.i" }

/-! ### The states, at each leaf's own `bind`

One name per link's target, in the form the link's own `denoteCode` leaves: the cell the
pivot or the leaf bound at the head of the environment, and the edge's `pc` and `pre`. -/

/-- `NodeBlock60`'s target on its set arm: `%Pivot61`'s bite, at `LeafBlock56`. -/
def ClsS56 (s : State) (x : BitVec 8) : State :=
  { ((HeadS60 s x).bind "%Pivot61" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 116)))) with
    pc := "LeafBlock56", pre := some (HeadS60 s x).pc }

/-- `LeafBlock56`'s target on its true arm: `%SwitchLeaf57`'s bite, at `if.then403.i`. -/
def ClsS403 (s : State) (x : BitVec 8) : State :=
  { ((ClsS56 s x).bind "%SwitchLeaf57" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 110)))) with
    pc := "if.then403.i", pre := some (ClsS56 s x).pc }

/-- `LeafBlock56`'s target on its else arm: the same bite, at `if.else405.i`. -/
def ClsS405 (s : State) (x : BitVec 8) : State :=
  { ((ClsS56 s x).bind "%SwitchLeaf57" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 110)))) with
    pc := "if.else405.i", pre := some (ClsS56 s x).pc }

/-- The true arm's target: `if.then403.i`'s empty body, at `if.then413.i`. -/
def ClsS413T (s : State) (x : BitVec 8) : State :=
  { ClsS403 s x with pc := "if.then413.i", pre := some (ClsS403 s x).pc }

/-- The else arm's target: `if.else405.i`'s empty body, at `if.then413.i`. -/
def ClsS413F (s : State) (x : BitVec 8) : State :=
  { ClsS405 s x with pc := "if.then413.i", pre := some (ClsS405 s x).pc }

/-- `LeafBlock58`'s target on its true arm: `%SwitchLeaf59`'s bite, at `if.then413.i`. -/
def ClsS58T (s : State) (x : BitVec 8) : State :=
  { ((HeadS58 s x).bind "%SwitchLeaf59" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 116)))) with
    pc := "if.then413.i", pre := some (HeadS58 s x).pc }

/-! ### The `%8` cells the pivots and the leaves read

Each block on the way binds one fresh name, so the byte at each is the span's entry's,
after `lookupName_cons_ne` at the bound name. -/

/-- `%8` at `NodeBlock60` is the span's entry's: `NodeBlock62` binds `%Pivot63` only. -/
theorem clsS60_env8 (s : State) (x : BitVec 8)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    evalOperand (HeadS60 s x) (.reg "%8") = some (.int 8 x) := by
  simp only [HeadS60, HeadS62, State.bind, evalOperand,
    lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
  exact h8

/-- `%8` at `LeafBlock56` is the span's entry's (`%Pivot63` and `%Pivot61` peeled). -/
theorem clsS56_env8 (s : State) (x : BitVec 8)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    evalOperand (ClsS56 s x) (.reg "%8") = some (.int 8 x) := by
  simp only [ClsS56, HeadS60, HeadS62, State.bind, evalOperand,
    lookupName_cons_ne (k := "%Pivot61") (n := "%8") _ _ (by decide),
    lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
  exact h8

/-- `%8` at `LeafBlock58` is the span's entry's, for the same two peels. -/
theorem clsS58_env8 (s : State) (x : BitVec 8)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x)) :
    evalOperand (HeadS58 s x) (.reg "%8") = some (.int 8 x) := by
  simp only [HeadS58, HeadS60, HeadS62, State.bind, evalOperand,
    lookupName_cons_ne (k := "%Pivot61") (n := "%8") _ _ (by decide),
    lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
  exact h8

/-! ### The spans

Each is the same three-link prefix — the empty body at `if.else387.i`, the first pivot's
clear arm, the second pivot's own arm — and then the leaf's bite and the empty body it
takes.  The prefix is repeated rather than factored because each span's target state is
the leaf's own `bind`, and a factored prefix would have to state it as an index the caller
re-derives. -/

/-- **`110`'s span**: `if.else387.i` to `if.then413.i` in five links, through
`LeafBlock56`'s *true* arm (`if.then403.i`, kind `10`). -/
theorem c56TrueSpan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h₁ : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h₃ : evalICmp .eq x (BitVec.ofNat 8 110) = 1) :
    Seg calls G C s ({ ClsC₄₀₃ C with block := "if.then413.i" }) (ClsS413T s x) 5 := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x) := h8
  -- 2. `NodeBlock62`, whose bit is clear
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "NodeBlock60" from by rw [h₁]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = HeadS60 s x := hs₂
  rw [hs₂'] at hl₂
  -- 3. `NodeBlock60`, whose bit is set
  have h8₂ : evalOperand (HeadS60 s x) (.reg "%8") = some (.int 8 x) := clsS60_env8 s x h8
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock60_at (calls := calls) (G := G)
    (C := HeadC₆₀ C) (s := HeadS60 s x) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 116) = 1 then "LeafBlock56"
    else "LeafBlock58") = "LeafBlock56" from by rw [h₂]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = ClsS56 s x := hs₃
  rw [hs₃'] at hl₃
  -- 4. `LeafBlock56`, whose equality test is set
  have h8₃ : evalOperand (ClsS56 s x) (.reg "%8") = some (.int 8 x) := clsS56_env8 s x h8
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock56_at (calls := calls) (G := G)
    (C := ClsC₅₆ C) (s := ClsS56 s x) hl₃.inv' rfl h8₃
  rw [show (if evalICmp .eq x (BitVec.ofNat 8 110) = 1 then "if.then403.i"
    else "if.else405.i") = "if.then403.i" from by rw [h₃]; rfl] at hs₄ hl₄
  have hs₄' : s₄ = ClsS403 s x := hs₄
  rw [hs₄'] at hl₄
  -- 5. the empty body at `if.then403.i`
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    walkIfThen403_at (calls := calls) (G := G) (C := ClsC₄₀₃ C) (s := ClsS403 s x)
      hl₄.inv' rfl
  have hs₅' : s₅ = ClsS413T s x := hs₅
  rw [hs₅'] at hl₅
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄
    (Seg.tail hl₅ (Seg.nil hl₅.inv')))))

/-- **`111 … 115`'s span**: the same five links through `LeafBlock56`'s *else* arm
(`if.else405.i`, kind `0`). -/
theorem c56ElseSpan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h₁ : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h₃ : evalICmp .eq x (BitVec.ofNat 8 110) = 0) :
    Seg calls G C s (HeadC₄₁₃ (ClsC₄₀₅ C)) (ClsS413F s x) 5 := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x) := h8
  -- 2. `NodeBlock62`, whose bit is clear
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "NodeBlock60" from by rw [h₁]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = HeadS60 s x := hs₂
  rw [hs₂'] at hl₂
  -- 3. `NodeBlock60`, whose bit is set
  have h8₂ : evalOperand (HeadS60 s x) (.reg "%8") = some (.int 8 x) := clsS60_env8 s x h8
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock60_at (calls := calls) (G := G)
    (C := HeadC₆₀ C) (s := HeadS60 s x) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 116) = 1 then "LeafBlock56"
    else "LeafBlock58") = "LeafBlock56" from by rw [h₂]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = ClsS56 s x := hs₃
  rw [hs₃'] at hl₃
  -- 4. `LeafBlock56`, whose equality test is clear
  have h8₃ : evalOperand (ClsS56 s x) (.reg "%8") = some (.int 8 x) := clsS56_env8 s x h8
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock56_at (calls := calls) (G := G)
    (C := ClsC₅₆ C) (s := ClsS56 s x) hl₃.inv' rfl h8₃
  rw [show (if evalICmp .eq x (BitVec.ofNat 8 110) = 1 then "if.then403.i"
    else "if.else405.i") = "if.else405.i" from by rw [h₃]; rfl] at hs₄ hl₄
  have hs₄' : s₄ = ClsS405 s x := hs₄
  rw [hs₄'] at hl₄
  -- 5. the empty body at `if.else405.i`
  obtain ⟨s₅, hl₅, hs₅⟩ := headChain_else405_at (calls := calls) G (HeadC₄₀₅ (ClsC₄₀₅ C))
    (ClsS405 s x) hl₄.inv' rfl
  have hs₅' : s₅ = ClsS413F s x := hs₅
  rw [hs₅'] at hl₅
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄
    (Seg.tail hl₅ (Seg.nil hl₅.inv')))))

/-- **`116`'s span**: `if.else387.i` to `if.then413.i` in four links, through
`LeafBlock58`'s *true* arm — the leaf reaches the call's block itself, so there is no
empty body between (kind `8`). -/
theorem c58TrueSpan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h₁ : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h₃ : evalICmp .eq x (BitVec.ofNat 8 116) = 1) :
    Seg calls G C s ({ HeadC₅₈ C with block := "if.then413.i" }) (ClsS58T s x) 4 := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x) := h8
  -- 2. `NodeBlock62`, whose bit is clear
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "NodeBlock60" from by rw [h₁]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = HeadS60 s x := hs₂
  rw [hs₂'] at hl₂
  -- 3. `NodeBlock60`, whose bit is clear
  have h8₂ : evalOperand (HeadS60 s x) (.reg "%8") = some (.int 8 x) := clsS60_env8 s x h8
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock60_at (calls := calls) (G := G)
    (C := HeadC₆₀ C) (s := HeadS60 s x) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .slt x (BitVec.ofNat 8 116) = 1 then "LeafBlock56"
    else "LeafBlock58") = "LeafBlock58" from by rw [h₂]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = HeadS58 s x := hs₃
  rw [hs₃'] at hl₃
  -- 4. `LeafBlock58`, whose equality test is set: the target is the call's block
  have h8₃ : evalOperand (HeadS58 s x) (.reg "%8") = some (.int 8 x) := clsS58_env8 s x h8
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock58_at (calls := calls) (G := G)
    (C := HeadC₅₈ C) (s := HeadS58 s x) hl₃.inv' rfl h8₃
  rw [show (if evalICmp .eq x (BitVec.ofNat 8 116) = 1 then "if.then413.i"
    else "if.else405.i") = "if.then413.i" from by rw [h₃]; rfl] at hs₄ hl₄
  have hs₄' : s₄ = ClsS58T s x := hs₄
  rw [hs₄'] at hl₄
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄ (Seg.nil hl₄.inv'))))

/-- **`117 … 125`'s span**, at this module's vocabulary: `walkHeadChainCSeg` is the same
five links through `LeafBlock58`'s *else* arm, already composed where the whitespace arm
needs it.  Stated here so the four leaf arms are one interface. -/
theorem c58ElseSpan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h₁ : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h₃ : evalICmp .eq x (BitVec.ofNat 8 116) = 0) :
    Seg calls G C s (HeadC₄₁₃ C) (HeadS413 s x) 5 :=
  walkHeadChainCSeg G C s hInv hblock h8 h₁ h₂ h₃

/-! ### The merge the four routes share

The tail's three calls and the merge's own step read the endpoint's invariant, its block
name and its `%t352.i` cell — nothing else — so one theorem serves all four spans, given
the span as a segment at `nS ≤ 5`.  The price is `nH + nS + 4 + 2 ≤ 32·Δk + 8·ΔA` at
`nH ≤ 12` and `nS ≤ 5`, with no byte term spent. -/
theorem classCMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
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
  -- the head's count, the span's and the tail's three
  have hsegH : WalkSegment (stage2Calls stage2SubCalls) G C s Cs ss (nH + nS) :=
    hHead.trans (Seg.measure hSpan)
  have hsegT : WalkSegment (stage2Calls stage2SubCalls) G C s Ct st (nH + nS + 3) :=
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
    { st with pc := "cleanup478.i", pre := some st.pc }, nH + nS + 4,
    hsegT.trans (WalkSegment.of_link hl₂), rfl, htk, ?_, ?_, ?_, ?_⟩
  · show (some st.pc : Option String) = some "if.end473.i"
    rw [hpc]
  · show lookupName st.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
    exact hinc
  · show lookupName st.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))
    exact hnep
  · -- the price: twelve and five links at their bounds, and the entry's allowance
    have hb : nH + nS + 4 + 2 ≤ 12 + 5 + 4 + 2 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one]
    omega

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.clsS60_env8
#print axioms LeanLLVM.Refinement.WalkScope.clsS56_env8
#print axioms LeanLLVM.Refinement.WalkScope.clsS58_env8
#print axioms LeanLLVM.Refinement.WalkScope.c56TrueSpan
#print axioms LeanLLVM.Refinement.WalkScope.c56ElseSpan
#print axioms LeanLLVM.Refinement.WalkScope.c58TrueSpan
#print axioms LeanLLVM.Refinement.WalkScope.c58ElseSpan
#print axioms LeanLLVM.Refinement.WalkScope.classCMerge_at

end WalkScope
end LeanLLVM.Refinement
