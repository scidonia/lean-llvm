/-
The head path's class-C span: `if.else387.i` to `if.then413.i`.

`if.end372.i`'s else arm reaches `if.else387.i` (`end372_else_chain`), and the next five
blocks are the walk's nested pivots on the byte in `%8`:

```
if.else387.i → NodeBlock62 → NodeBlock60 → LeafBlock58 → if.else405.i → if.then413.i
```

Three of them are class A — one `icmp` into a fresh name and a `condbr` on its bit — and
two are class B, an empty body and a `br`.  Each class has its link already
(`WalkLink.NodeBlock62`/`_at`, `WalkLink.if_else387_i`, …), so the span is composition:
what is owed is the chain, its carries and the states a link's target has to be named at.

**The arms, and the byte they describe.**  The span is the walk's decision that the byte
in `%8` is *above* `'t'`: `NodeBlock62`'s `icmp slt i8 %8, 110` is clear, so the pivot
goes to `NodeBlock60`; its `icmp slt i8 %8, 116` is clear, so the second pivot goes to
`LeafBlock58`; and its `icmp eq i8 %8, 116` is clear, so the leaf goes to `if.else405.i`,
whose empty body jumps to `if.then413.i`.  A byte of 117 or more takes all three, and the
three bit hypotheses are the caller's, not facts of the terminator
(`walkIcmpBrStep`'s shape).

**What the span owes beyond its links.**  Three things, and each is a spelling the layers
already fixed.  The carries are the nested `with`-updates the links produce, and a nest at
depth three is not a term a named argument can hold, so each one is an `abbrev`
(`HeadC₆₂` … `HeadC₄₁₃`) — the reason `ScanC₁₀₅` and `FinishC₄₈₈` exist.  The states the
pivots leave are `have`-bound `bind` nests, so each is a `def` (`HeadS62` … `HeadS413`),
which is what makes a link's `rfl` against the next link's source possible at all.  And the
two empty blocks have no `_at` lemma here: their step binds nothing, so the successor is
`{ s with pc := …, pre := some s.pc }` and the named state is one `walkBrStep` and
`Ctrl.jump`'s injectivity away, which is what the two lemmas below state.

The chain starts at its caller's own `if.else387.i` entry state and ends at the name
`HeadS413`, with `WalkInv` at every link — so a consumer appends its next step at
`if.then413.i` with `WalkChain.append`, and the fits are `rfl`s because every carry and
state on the way is a name rather than a literal.
-/
import LeanLLVM.Refinement.JsonStage2WalkSteps

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The carries

`if.else387.i`'s target, and then one name per pivot.  The `with`-nest grows by one level
per link, and a nest at depth ≥ 2 cannot be written as a named argument, so the `abbrev`
is the only spelling a client or a `rfl` can use.
-/

/-- The carry after `if.else387.i`'s edge: the first pivot. -/
abbrev HeadC₆₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock62" }

/-- The carry at the second pivot. -/
abbrev HeadC₆₀ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadC₆₂ C with block := "NodeBlock60" }

/-- The carry at the leaf. -/
abbrev HeadC₅₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadC₆₀ C with block := "LeafBlock58" }

/-- The carry at the leaf's else arm. -/
abbrev HeadC₄₀₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadC₅₈ C with block := "if.else405.i" }

/-- The carry at `if.then413.i`, where the value-position call stands. -/
abbrev HeadC₄₁₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadC₄₀₅ C with block := "if.then413.i" }

/-! ### The states

One name per link's target, in the form the link's own `denoteCode` leaves: the cell the
pivot bound at the head of the environment, and the edge's `pc` and `pre`.  A `def` and
not an `abbrev`, because a chain's state is an index and an index is unified
syntactically.
-/

/-- `if.else387.i`'s target: the empty body's edge to `NodeBlock62`. -/
def HeadS62 (s : State) : State :=
  { s with pc := "NodeBlock62", pre := some s.pc }

/-- `NodeBlock62`'s target: `%Pivot63`'s bite on the arm to `NodeBlock60`. -/
def HeadS60 (s : State) (x1 : BitVec 8) : State :=
  { ((HeadS62 s).bind "%Pivot63"
      (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 110)))) with
    pc := "NodeBlock60", pre := some (HeadS62 s).pc }

/-- `NodeBlock60`'s target: `%Pivot61`'s bite on the arm to `LeafBlock58`. -/
def HeadS58 (s : State) (x1 : BitVec 8) : State :=
  { ((HeadS60 s x1).bind "%Pivot61"
      (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 116)))) with
    pc := "LeafBlock58", pre := some (HeadS60 s x1).pc }

/-- `LeafBlock58`'s target: `%SwitchLeaf59`'s bite on the arm to `if.else405.i`. -/
def HeadS405 (s : State) (x1 : BitVec 8) : State :=
  { ((HeadS58 s x1).bind "%SwitchLeaf59"
      (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 116)))) with
    pc := "if.else405.i", pre := some (HeadS58 s x1).pc }

/-- `if.else405.i`'s target: the empty body's edge to `if.then413.i`. -/
def HeadS413 (s : State) (x1 : BitVec 8) : State :=
  { (HeadS405 s x1) with pc := "if.then413.i", pre := some (HeadS405 s x1).pc }

/-! ### The two empty bodies, at their named targets

A class-B block's link returns its witness existentially while the chain needs the
target as an index.  The block's `br` names the successor outright (`walkBrStep`), so the
witness is that state by `Ctrl.jump`'s injectivity — the identification
`walkIfElse387_at` and `walkIfThen403_at` make for the same two blocks at their other
arms.
-/

/-- **`if.else387.i`'s target, named.**  An empty body and one `br`, so the target is the
source with the edge's successor, and the environment is untouched. -/
theorem headChain_else387_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i") :
    ∃ (s' : State), WalkLink calls G C s (HeadC₆₂ C) s' ∧ s' = HeadS62 s := by
  obtain ⟨s', hl⟩ := WalkLink.if_else387_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_else387_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_else387_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_else387_i)
    (dest := "NodeBlock62") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.else405.i`'s target, named.**  The same shape at the leaf's else arm; the
successor is `if.then413.i`. -/
theorem headChain_else405_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else405.i") :
    ∃ (s' : State), WalkLink calls G C s (HeadC₄₁₃ C) s' ∧
      s' = { s with pc := "if.then413.i", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_else405_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_else405_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_else405_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_else405_i)
    (dest := "if.then413.i") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-! ### The span

The chain's five links.  Each link's bit hypothesis resolves the arm its successor names,
which is what turns the link's `if`-shaped carry and `pc` into the next link's `rfl`, and
each pivot's `%8` fact is the previous one *peeled*: the step binds one cell, so the read
at the target is the source's fact after `lookupName_cons_ne` at the bound name.
-/

/-- **The class-C span of the head path**, from `if.else387.i`'s entry to
`if.then413.i`'s: the three nested pivots on `%8` and the two empty bodies between them.

The byte is above `'t'` — `110 ≤ %8`, then `116 ≤ %8`, then `%8 ≠ 116` — so the walk
takes the three else arms in a row and arrives at the value-position call's block.  The
conclusion names both ends (`HeadC₄₁₃` and `HeadS413`), so the call's step appends here
and `if.end372.i`'s else arm appends before it. -/
theorem walkHeadChainC {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x1 : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x1))
    (h₁ : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h₃ : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    WalkChain calls G C s (HeadC₄₁₃ C) (HeadS413 s x1) := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x1) := h8
  -- 2. `NodeBlock62`, whose bit is clear
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "NodeBlock60" from by rw [h₁]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = HeadS60 s x1 := hs₂
  rw [hs₂'] at hl₂
  have h8₂ : evalOperand (HeadS60 s x1) (.reg "%8") = some (.int 8 x1) := by
    simp only [HeadS60, HeadS62, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
    exact h8
  -- 3. `NodeBlock60`, whose bit is clear
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock60_at (calls := calls) (G := G)
    (C := HeadC₆₀ C) (s := HeadS60 s x1) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock56"
    else "LeafBlock58") = "LeafBlock58" from by rw [h₂]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = HeadS58 s x1 := hs₃
  rw [hs₃'] at hl₃
  have h8₃ : evalOperand (HeadS58 s x1) (.reg "%8") = some (.int 8 x1) := by
    simp only [HeadS58, HeadS60, HeadS62, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot61") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
    exact h8
  -- 4. `LeafBlock58`, whose bit is clear
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock58_at (calls := calls) (G := G)
    (C := HeadC₅₈ C) (s := HeadS58 s x1) hl₃.inv' rfl h8₃
  rw [show (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.then413.i"
    else "if.else405.i") = "if.else405.i" from by rw [h₃]; rfl] at hs₄ hl₄
  have hs₄' : s₄ = HeadS405 s x1 := hs₄
  rw [hs₄'] at hl₄
  -- 5. the empty body at `if.else405.i`
  obtain ⟨s₅, hl₅, hs₅⟩ := headChain_else405_at (calls := calls) G (HeadC₄₀₅ C)
    (HeadS405 s x1) hl₄.inv' rfl
  have hs₅' : s₅ = HeadS413 s x1 := hs₅
  rw [hs₅'] at hl₅
  exact WalkChain.tail hl₁ (WalkChain.tail hl₂ (WalkChain.tail hl₃
    (WalkChain.tail hl₄ (WalkChain.tail hl₅ (WalkChain.nil hl₅.inv')))))

end WalkScope
end LeanLLVM.Refinement
