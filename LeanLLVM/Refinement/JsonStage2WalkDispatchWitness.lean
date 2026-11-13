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

/-! ### The refusal's own two blocks

`if.then53.i` tests the depth register and `if.then56.i` records the entry's
position in `%e + 8`.  The store is the block whose successor *is* the refusal copy,
so the segment's target state is this block's own conclusion rather than a `pc` the
next block reads. -/

/-- `if.then56.i`: the entry's position written at `%e + 8`, at `if.then`. -/
def refuseS₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State) : State :=
  { { s with
      env := ("%off1.i.i41", .ptr (C.stage.e + 8)) :: s.env
      mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s.pc }

/-- **`if.then53.i` at depth zero.**  `%sp.i.0248 = 0` — the invariant's own
`depth_reg` at `C.sp = 0` — is true, so the run takes `if.then56.i`. -/
theorem refuseStep₅ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then53.i")
    (hsp : C.sp = 0) :
    WalkLink calls G C s { C with block := "if.then56.i" } (refuseS₅ s) := by
  have h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 0)) := by
    simpa only [evalOperand, hsp] using hInv.depth_reg
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then53_i_at G C s hInv hblock h1
  have hbit : evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = 1 := by decide
  have hstate : s' = refuseS₅ s := hs'.trans (by simp [refuseS₅, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.then56.i`.**  The refusal's offset store: the entry's position goes to
`%e + 8` and the edge is the refusal copy, so the carry's `eoff` is the position the
store wrote — the same number the document's own bound covers. -/
theorem refuseStep₆ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then56.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (refuseS₆ C j s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then56_i_at G C s hInv hblock hv he hj hj64
  rw [hs'] at hl
  simpa only [refuseS₆] using hl

/-! ### The witness

The six links composed at their own count.  `Seg` is the trace vocabulary's counted
form (`JsonStage2WalkInduce`), so the price is the segment's index — six — and not a
number read off a `Prop`'s shape. -/

/-- **The closing-bracket refusal, as one counted run.**  The head's three pivots,
the leaf's equality, the depth test and the offset store: six links from
`walkLoopHead` to `if.then`, at the cells each block's successor reads. -/
theorem bracketRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  -- the byte, at each switch state: one cell per block, and `%8` is not one of them
  have h8₁ : evalOperand (refuseS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (refuseS₂ (refuseS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [refuseS₂, refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (refuseS₃ (refuseS₂ (refuseS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [refuseS₃, refuseS₂, refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  -- the position and the refusal record, through the five cells the path binds
  have hv₅ : evalOperand (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))))
      (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)) := by
    simpa only [refuseS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf10") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot12") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%idxprom.i") _ _ (by decide)] using hv
  have he₅ : lookupName (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))).env "%e" =
      some (.ptr C.stage.e) := by
    simpa only [refuseS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, State.bind,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf10") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot12") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)] using he
  -- the six links, each at the state the previous one names
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock19" } (refuseS₁ s) :=
    refuseStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock19" } (refuseS₁ s)
      { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s)) :=
    refuseStep₂ G { C with block := "NodeBlock19" } (refuseS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s))
      { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s))) :=
    refuseStep₃ G { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s)))
      { C with block := "if.then53.i" } (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) :=
    refuseStep₄ G { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s)))
      L₃.inv' rfl h8₃
  have L₅ : WalkLink calls G { C with block := "if.then53.i" }
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))
      { C with block := "if.then56.i" }
      (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) :=
    refuseStep₅ G { C with block := "if.then53.i" }
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) L₄.inv' rfl hsp
  have L₆ : WalkLink calls G { C with block := "if.then56.i" }
      (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))))
      { C with block := "if.then", eoff := j, refusal := true }
      (refuseS₆ C j (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))))) :=
    refuseStep₆ G { C with block := "if.then56.i" }
      (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) L₅.inv' rfl hv₅ he₅ hj hj64
  refine ⟨{ C with block := "if.then", eoff := j, refusal := true },
    refuseS₆ C j (refuseS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))), 6, ?_, rfl,
    L₆.inv'.eoff_le, refusePrice_six G C hk⟩
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
    (Seg.tail L₅ (Seg.tail L₆ (Seg.nil L₆.inv')))))))

/-- **The `refuse` witness at a depth-zero closing bracket**, in the exact shape
`WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct.  Six
blocks from the head to the refusal copy, the offset the store wrote, and the price
inside one entry's allowance and the document's remaining bytes.

A closing bracket at depth zero is the refusal the old `C.k + 1 < G.nep` split
could not describe: the dispatch is refused while entries remain, and no revolution
follows. -/
theorem walkRefuseWitness_bracket {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  bracketRefuse_at G C s hInv hhead h8 hsp hv he hj hj64 hk

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.refusePrice_six
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₁
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₂
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₃
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₄
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₅
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₆
#print axioms LeanLLVM.Refinement.WalkScope.bracketRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_bracket
