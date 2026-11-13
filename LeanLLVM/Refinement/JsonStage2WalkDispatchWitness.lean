import LeanLLVM.Refinement.JsonStage2WalkChain
import LeanLLVM.Refinement.JsonStage2WalkInduce

/-! # The `refuse` witness, run block by block

`WalkDispatchThree.ofContinueAndLast` (`JsonStage2WalkAssembly`) takes the last
entry's two cases as an obligation: at `¬ (C.k + 1 < G.nep)` the dispatch either
finishes at the terminal index or refuses before the merge, and the `refuse`
alternative is

  `∃ Cd sd p, WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧
    Cd.eoff ≤ G.n ∧ p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k)`.

This module proves that alternative at a branch that produces it.  The dispatch's
proof is not a chain of `WalkLink`s: a link's target is existential, so a chain
leaves the state at the refusal copy unnamed and the price says nothing (that
module's own note, "What a dispatch proof still owes").  A dispatch proof is a
per-block run at the *values the next block reads*, so each block below is one
`WalkLink` whose source and target states are named (`refuseS₁` … `refuseS₆`), the
successor's environment is the predecessor's plus one cell, and the branch is
resolved by the bit its `icmp` computes at the byte the run carries.

**The branch.**  A depth-zero closing bracket is refused with entries remaining:
the switch's pivots take `NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock9`,
`if.then53.i` tests the depth register and takes `if.then56.i`, and that block
stores the entry's position in `%e + 8` and jumps to the refusal copy `if.then` —
six blocks from the head, inside one entry's allowance (`refusePrice_six`).

**What is not here.**  The other refusal branches (`if.then205.i`, the string
opener at the last entry; `if.then71.i`, `cleanup104.i` and the mismatched
literals; the four trap blocks), and the `finish` alternative.  Each is the same
shape: a path of named per-block runs from `walkLoopHead`, which is why they are
stated as branches of one `WalkRefuseAt` and not as one theorem over the token. -/

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-! ### The alternative, as a predicate

`WalkDispatchThree.ofContinueAndLast`'s `hlast` writes the two terminal outcomes as
anonymous existentials.  Naming the refusal one gives each branch a single goal
shape, so a branch theorem says what it is: a segment from the head to the refusal
copy, with the offset inside the document and the price inside the entry's credit. -/

/-- **The `refuse` alternative.**  A counted segment from the head to `if.then` —
the refusal copy — at an offset inside the document, and a price inside the
remaining entries' and bytes' credit.  `WalkSegment.ret` and the exit's tail take it
from there; this module supplies it at one branch. -/
def WalkRefuseAt (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) : Prop :=
  ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
    WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
    p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k)

/-- **Six blocks are inside one entry's credit.**  The refusal path is six control
steps, and the price it must fit is `32·Δk + 8·ΔA`; with one entry still unconsumed
the entry term alone is `32`.  The byte term is left where it is: the refusal reads
one byte of the document and decodes nothing, so no decoded extent has to be
charged. -/
theorem refusePrice_six {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (hk : C.k < G.nep) :
    6 + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k) := by
  have h : 1 ≤ G.nep - C.k := by omega
  have hmul : stage2EntryAllowance * 1 ≤ stage2EntryAllowance * (G.nep - C.k) :=
    Nat.mul_le_mul_left _ h
  simp only [stage2EntryAllowance] at hmul ⊢
  omega

/-! ### The path's states

Each is the state its block leaves: the block's own cell, at the successor's `pc` and
with the predecessor's `pre`.  They are the literal terms the `_at` instances name, so
the instance's state equality is `rfl` past the bit the branch takes, and the segment
below never carries the environment nest in its own statement. -/

/-- `NodeBlock21` at `%8 = 93`: `%8 < 91` is false, so the edge is `NodeBlock19`. -/
def refuseS₁ (s : State) : State :=
  { s.bind "%Pivot22" (.int 1 (0 : BitVec 1)) with pc := "NodeBlock19", pre := some s.pc }

/-- `NodeBlock19` at `%8 = 93`: `%8 < 123` is true, so the edge is `NodeBlock11`. -/
def refuseS₂ (s : State) : State :=
  { s.bind "%Pivot20" (.int 1 (1 : BitVec 1)) with pc := "NodeBlock11", pre := some s.pc }

/-- `NodeBlock11` at `%8 = 93`: `%8 < 93` is false, so the edge is `LeafBlock9`. -/
def refuseS₃ (s : State) : State :=
  { s.bind "%Pivot12" (.int 1 (0 : BitVec 1)) with pc := "LeafBlock9", pre := some s.pc }

/-- `LeafBlock9` at `%8 = 93`: `%8 = 93` is true, so the edge is `if.then53.i`. -/
def refuseS₄ (s : State) : State :=
  { s.bind "%SwitchLeaf10" (.int 1 (1 : BitVec 1)) with
    pc := "if.then53.i", pre := some s.pc }

/-- `if.then53.i` at a depth-zero register: `%sp.i.0248 = 0` is true, so the edge is
`if.then56.i`. -/
def refuseS₅ (s : State) : State :=
  { s.bind "%cmp54.i" (.int 1 (1 : BitVec 1)) with pc := "if.then56.i", pre := some s.pc }

/-! ### The path's blocks

One link per block, at the state the block's `_at` instance names.  The branch's bit
is `decide`d at the literal operands, and the successor state is the `def` above, so
the step is the instance's own equality and nothing is re-derived. -/

/-- **`NodeBlock21` at a closing bracket.**  The first pivot of the switch:
`%8 < 91` is false at `93`, so the run leaves the head at `NodeBlock19`. -/
theorem refuseStep₁ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93))) :
    WalkLink calls G C s { C with block := "NodeBlock19" } (refuseS₁ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 93) (BitVec.ofNat 8 91) = 0 := by decide
  have hstate : s' = refuseS₁ s := hs'.trans (by simp [refuseS₁, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock19` at a closing bracket.**  `%8 < 123` is true at `93`, so the run
leaves `NodeBlock19` at `NodeBlock11`. -/
theorem refuseStep₂ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock19")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93))) :
    WalkLink calls G C s { C with block := "NodeBlock11" } (refuseS₂ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock19_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 93) (BitVec.ofNat 8 123) = 1 := by decide
  have hstate : s' = refuseS₂ s := hs'.trans (by simp [refuseS₂, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock11` at a closing bracket.**  `%8 < 93` is false at `93` — the
switch's own boundary is exclusive — so the run leaves `NodeBlock11` at
`LeafBlock9`. -/
theorem refuseStep₃ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock11")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93))) :
    WalkLink calls G C s { C with block := "LeafBlock9" } (refuseS₃ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock11_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 93) (BitVec.ofNat 8 93) = 0 := by decide
  have hstate : s' = refuseS₃ s := hs'.trans (by simp [refuseS₃, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`LeafBlock9` at a closing bracket.**  The leaf's equality test is true at
`93`, so the run takes the switch's own arm, `if.then53.i`. -/
theorem refuseStep₄ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "LeafBlock9")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93))) :
    WalkLink calls G C s { C with block := "if.then53.i" } (refuseS₄ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.LeafBlock9_at G C s hInv hblock h8
  have hbit : evalICmp .eq (BitVec.ofNat 8 93) (BitVec.ofNat 8 93) = 1 := by decide
  have hstate : s' = refuseS₄ s := hs'.trans (by simp [refuseS₄, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl
