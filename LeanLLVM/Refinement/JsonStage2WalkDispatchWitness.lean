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

This module proves that alternative at two branches that produce it.  The
dispatch's proof is not a chain of `WalkLink`s: a link's target is existential, so
a chain leaves the state at the refusal copy unnamed and the price says nothing
(that module's own note, "What a dispatch proof still owes").  A dispatch proof is
a per-block run at the *values the next block reads*, so each block below is one
`WalkLink` whose source and target states are named (`refuseS₁` … `refuseS₆`,
`quoteS₁` … `refuseStore205Out`), the successor's environment is the predecessor's
plus one cell, and the branch is resolved by the bit its `icmp` computes at the byte
the run carries.

**The branches.**

* a depth-zero closing bracket, refused with entries remaining:
  `NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock9 → if.then53.i →
  if.then56.i → if.then` — six blocks, the offset being the entry's own position;
* a string opener with no entries left: `NodeBlock21 → NodeBlock5 → LeafBlock →
  sw.bb202.i → if.then205.i → if.then` — five blocks, the offset being the
  document's length.  This is the branch `hlast`'s own hypothesis selects, since
  `¬ (C.k + 1 < G.nep)` at `%inc.i = C.k + 1` is `sw.bb202.i`'s negated test.

Both prices are one bound (`refusePrice_of_le`): a refusal path is at most thirty
steps, so with one entry unconsumed the entry term alone pays for it.

**An open point: the past-end entry.**  Every theorem here carries
`hk : C.k < G.nep`; it is not derived, because `WalkInv` records only `C.k ≤ G.nep`.
At `C.k = G.nep` the price's byte term starts from `entryPos G G.nep`, which the
totalisation sends to `0` and which then has to pay for a whole document rather than
for a span — the accounting the review handoff raised as open (a terminal charge
reading a past-end entry).  `entryPos` and `entryByte` state the position at which
the default is read, and say of it that "the carrier is read at an index the loop's
own bound keeps inside the stream, so the default is a totalisation, not a case the
walk takes": the loop's own guard is `C.k < G.nep`.  Whether the past-end state is
in the invariant's scope, and on which credit boundary it is charged, is a design
question about the terminal price — it is not settled here, and a witness file is not
where it should be.

**What is not here.**  The remaining refusal branches — `if.then71.i`,
`cleanup104.i`, `if.then13.i`/`if.then176.i`, the mismatched literals' — and the
`four` trap blocks (`walkTrap_noStep`), plus the `finish` alternative.  Each is the
same shape: named per-block runs from `walkLoopHead`, which is why they are stated
as branches of one `WalkRefuseAt` rather than as one theorem over the token.  The
general `hlast` obligation is the case split over `%8` that selects among them, and
this module does not state it. -/

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

/-- **A refusal path shorter than the entry's credit.**  The price a refusal must fit
is `32·Δk + 8·ΔA`; with one entry still unconsumed the entry term alone is `32`, so
every path of at most thirty steps fits it, and the branch's own byte term is left
where it is: the refusal reads a byte of the document and decodes nothing, so no
decoded extent has to be charged. -/
theorem refusePrice_of_le {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {p : Nat}
    (hp : p ≤ 30) (hk : C.k < G.nep) :
    p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
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
    L₆.inv'.eoff_le, refusePrice_of_le G C (by omega) hk⟩
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

/-! ### The string opener's refusal, at the last entry

The second refusal branch the dispatch note names: `%8 = 34` takes the switch's
`LeafBlock → sw.bb202.i` arm, and `sw.bb202.i` tests `%inc.i < %nep` — a string opener
needs a closing entry, so with none left the block stores the document's length in
`%e + 8` and jumps to the refusal copy.  Its condition is `hlast`'s own
(`¬ (C.k + 1 < G.nep)`, at `%inc.i = C.k + 1`), not a bound the caller adds.

Every state is written at its own input, so each `_at` instance's `pre := some s.pc`
is the `def`'s own term and the block's equality is `rfl` past the branch's bit. -/

/-- **`%inc.i < %nep` is false at the last entry.**  `evalICmp`'s unsigned comparison
on `ofNat` operands is the natural order, so the negated bound is the bit. -/
theorem refuseUlt_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ¬ a < b) :
    evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0 := by
  have hu : BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
    rw [BitVec.ult]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact decide_eq_false h
  simp only [evalICmp, hu]
  rfl

/-- `NodeBlock21` at `%8 = 34`: `%8 < 91` is true, so the edge is `NodeBlock5`. -/
def quoteS₁ (s : State) : State :=
  { s.bind "%Pivot22" (.int 1 (1 : BitVec 1)) with pc := "NodeBlock5", pre := some s.pc }

/-- `NodeBlock5` at `%8 = 34`: `%8 < 44` is true, so the edge is `LeafBlock`. -/
def quoteS₂ (s : State) : State :=
  { s.bind "%Pivot6" (.int 1 (1 : BitVec 1)) with pc := "LeafBlock", pre := some s.pc }

/-- `LeafBlock` at `%8 = 34`: `%8 = 34` is true, so the edge is `sw.bb202.i`. -/
def quoteS₃ (s : State) : State :=
  { s.bind "%SwitchLeaf" (.int 1 (1 : BitVec 1)) with
    pc := "sw.bb202.i", pre := some s.pc }

/-- `sw.bb202.i` at the last entry: `%inc.i < %nep` is false, so the edge is
`if.then205.i`. -/
def quoteS₄ (s : State) (inc nep : BitVec 64) : State :=
  { s.bind "%cmp203.not.i" (.int 1 (evalICmp .ult inc nep)) with
    pc := "if.then205.i", pre := some s.pc }

/-- `if.then205.i`'s successor: the document's length at `%e + 8`, at the copy. -/
def refuseStore205Out {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat)
    (s : State) : State :=
  { { s with
      env := ("%off1.i.i76", .ptr (C.stage.e + 8)) :: s.env
      mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s.pc }

/-- **`NodeBlock21` at a quote.**  `%8 < 91` is true at `34`, so the run leaves the
head at `NodeBlock5`. -/
theorem quoteRefuseStep₁ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34))) :
    WalkLink calls G C s { C with block := "NodeBlock5" } (quoteS₁ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 91) = 1 := by decide
  have hstate : s' = quoteS₁ s := hs'.trans (by simp [quoteS₁, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock5` at a quote.**  `%8 < 44` is true at `34`, so the run leaves
`NodeBlock5` at `LeafBlock`. -/
theorem quoteRefuseStep₂ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock5")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34))) :
    WalkLink calls G C s { C with block := "LeafBlock" } (quoteS₂ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock5_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 44) = 1 := by decide
  have hstate : s' = quoteS₂ s := hs'.trans (by simp [quoteS₂, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`LeafBlock` at a quote.**  The leaf's equality test is true at `34`, so the run
takes the string-opener arm, `sw.bb202.i`. -/
theorem quoteRefuseStep₃ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "LeafBlock")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34))) :
    WalkLink calls G C s { C with block := "sw.bb202.i" } (quoteS₃ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.LeafBlock_at G C s hInv hblock h8
  have hbit : evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 34) = 1 := by decide
  have hstate : s' = quoteS₃ s := hs'.trans (by simp [quoteS₃, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`sw.bb202.i` at the last entry.**  `%inc.i < %nep` is false, so the run takes
`if.then205.i` — the refusal, not the merge's arm. -/
theorem quoteRefuseStep₄ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "sw.bb202.i")
    {inc nep : BitVec 64}
    (hinc : evalOperand s (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand s (.reg "%nep") = some (.int 64 nep))
    (hbit : evalICmp .ult inc nep = 0) :
    WalkLink calls G C s { C with block := "if.then205.i" } (quoteS₄ s inc nep) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.sw_bb202_i_at G C s hInv hblock hinc hnep
  have hstate : s' = quoteS₄ s inc nep := hs'.trans (by simp [quoteS₄, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.then205.i` at the last entry.**  The document's length is stored at `%e + 8`
and the edge is the refusal copy. -/
theorem quoteRefuseStep₅ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then205.i")
    (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 G.n)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hn64 : G.n < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := G.n, refusal := true }
      (refuseStore205Out C G.n s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then205_i_at G C s hInv hblock hv he (le_refl G.n) hn64
  rw [hs'] at hl
  exact hl

/-- **The string opener's refusal, as one counted run.**  Five links from the head to
`if.then`: the switch's two pivots and the leaf's equality, the count test, and the
offset store. -/
theorem quoteRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)))
    {inc nep : BitVec 64}
    (hinc : evalOperand s (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand s (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 G.n)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e)) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  -- the byte, at the three states the switch binds into
  have h8₁ : evalOperand (quoteS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)) := by
    simpa only [quoteS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (quoteS₂ (quoteS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 34)) := by
    simpa only [quoteS₂, quoteS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (quoteS₃ (quoteS₂ (quoteS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 34)) := by
    simpa only [quoteS₃, quoteS₂, quoteS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  -- the count's two operands at the test's state, and the offset's two at the store
  have hinc₄ : evalOperand (quoteS₃ (quoteS₂ (quoteS₁ s))) (.reg "%inc.i") =
      some (.int 64 inc) := by
    simpa only [quoteS₃, quoteS₂, quoteS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%inc.i") _ _ (by decide)] using hinc
  have hnep₄ : evalOperand (quoteS₃ (quoteS₂ (quoteS₁ s))) (.reg "%nep") =
      some (.int 64 nep) := by
    simpa only [quoteS₃, quoteS₂, quoteS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%nep") _ _ (by decide)] using hnep
  have hv₅ : evalOperand (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep) (.reg "%4") =
      some (.int 64 (BitVec.ofNat 64 G.n)) := by
    simpa only [quoteS₄, quoteS₃, quoteS₂, quoteS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%cmp203.not.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%4") _ _ (by decide)] using hv
  have he₅ : lookupName (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep).env "%e" =
      some (.ptr C.stage.e) := by
    simpa only [quoteS₄, quoteS₃, quoteS₂, quoteS₁, State.bind,
      lookupName_cons_ne (k := "%cmp203.not.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)] using he
  -- the five links, each at the state the previous one names
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock5" } (quoteS₁ s) :=
    quoteRefuseStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock5" } (quoteS₁ s)
      { C with block := "LeafBlock" } (quoteS₂ (quoteS₁ s)) :=
    quoteRefuseStep₂ G { C with block := "NodeBlock5" } (quoteS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "LeafBlock" } (quoteS₂ (quoteS₁ s))
      { C with block := "sw.bb202.i" } (quoteS₃ (quoteS₂ (quoteS₁ s))) :=
    quoteRefuseStep₃ G { C with block := "LeafBlock" } (quoteS₂ (quoteS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "sw.bb202.i" } (quoteS₃ (quoteS₂ (quoteS₁ s)))
      { C with block := "if.then205.i" } (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep) :=
    quoteRefuseStep₄ G { C with block := "sw.bb202.i" } (quoteS₃ (quoteS₂ (quoteS₁ s)))
      L₃.inv' rfl hinc₄ hnep₄ hge
  have L₅ : WalkLink calls G { C with block := "if.then205.i" }
      (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep)
      { C with block := "if.then", eoff := G.n, refusal := true }
      (refuseStore205Out C G.n (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep)) :=
    quoteRefuseStep₅ G { C with block := "if.then205.i" }
      (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep) L₄.inv' rfl hv₅ he₅
      (WalkGeom.n_lt G)
  refine ⟨{ C with block := "if.then", eoff := G.n, refusal := true },
    refuseStore205Out C G.n (quoteS₄ (quoteS₃ (quoteS₂ (quoteS₁ s))) inc nep), 5, ?_, rfl,
    L₅.inv'.eoff_le, refusePrice_of_le G C (by omega) hk⟩
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
    (Seg.tail L₅ (Seg.nil L₅.inv'))))))

/-- **The `refuse` witness at a string opener with no entries left**, in the exact
shape `WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct.
Five blocks from the head to the refusal copy, the document's length as the offset,
and the price inside one entry's allowance.

This is the branch `hlast`'s own hypothesis selects: `¬ (C.k + 1 < G.nep)` at
`%inc.i = C.k + 1` is exactly `sw.bb202.i`'s negated test, so the run is the dispatch
refusing on the terminal entry rather than a caller-supplied bound. -/
theorem walkRefuseWitness_quote {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)))
    {inc nep : BitVec 64}
    (hinc : evalOperand s (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand s (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 G.n)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e)) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  quoteRefuse_at G C s hInv hhead h8 hinc hnep hge hv he hk

/-! ### The colon at depth zero

`%8 = 58` falls below `NodeBlock5`'s pivot and is not `44`, so the switch reaches
`NodeBlock → LeafBlock3`, whose equality test takes `if.then173.i`; a depth-zero
register there refuses with the entry's position in `%e + 8`.  Six blocks, and the
byte is the one the *dispatch* reads — an early refusal with entries remaining, which
is the case the old index split could not describe. -/

/-- `NodeBlock21` at `%8 = 58`: `%8 < 91` is true, so the edge is `NodeBlock5`. -/
def colS₁ (s : State) : State :=
  { s.bind "%Pivot22" (.int 1 (1 : BitVec 1)) with pc := "NodeBlock5", pre := some s.pc }

/-- `NodeBlock5` at `%8 = 58`: `%8 < 44` is false, so the edge is `NodeBlock`. -/
def colS₂ (s : State) : State :=
  { s.bind "%Pivot6" (.int 1 (0 : BitVec 1)) with pc := "NodeBlock", pre := some s.pc }

/-- `NodeBlock` at `%8 = 58`: `%8 < 58` is false, so the edge is `LeafBlock3`. -/
def colS₃ (s : State) : State :=
  { s.bind "%Pivot" (.int 1 (0 : BitVec 1)) with pc := "LeafBlock3", pre := some s.pc }

/-- `LeafBlock3` at `%8 = 58`: `%8 = 58` is true, so the edge is `if.then173.i`. -/
def colS₄ (s : State) : State :=
  { s.bind "%SwitchLeaf4" (.int 1 (1 : BitVec 1)) with
    pc := "if.then173.i", pre := some s.pc }

/-- `if.then173.i` at a depth-zero register: the edge is `if.then176.i`. -/
def colS₅ (s : State) : State :=
  { s.bind "%cmp174.i" (.int 1 (1 : BitVec 1)) with pc := "if.then176.i", pre := some s.pc }

/-- `if.then176.i`: the entry's position written at `%e + 8`, at `if.then`. -/
def colS₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State) : State :=
  { { s with
      env := ("%off1.i.i72", .ptr (C.stage.e + 8)) :: s.env
      mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s.pc }

/-- **`NodeBlock21` at a colon.**  `%8 < 91` is true at `58`. -/
theorem colStep₁ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58))) :
    WalkLink calls G C s { C with block := "NodeBlock5" } (colS₁ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 58) (BitVec.ofNat 8 91) = 1 := by decide
  have hstate : s' = colS₁ s := hs'.trans (by simp [colS₁, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock5` at a colon.**  `%8 < 44` is false at `58`, so the edge is
`NodeBlock`. -/
theorem colStep₂ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock5")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58))) :
    WalkLink calls G C s { C with block := "NodeBlock" } (colS₂ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock5_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 58) (BitVec.ofNat 8 44) = 0 := by decide
  have hstate : s' = colS₂ s := hs'.trans (by simp [colS₂, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock` at a colon.**  `%8 < 58` is false at `58` — the pivot's boundary is
exclusive — so the edge is `LeafBlock3`. -/
theorem colStep₃ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58))) :
    WalkLink calls G C s { C with block := "LeafBlock3" } (colS₃ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 58) (BitVec.ofNat 8 58) = 0 := by decide
  have hstate : s' = colS₃ s := hs'.trans (by simp [colS₃, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`LeafBlock3` at a colon.**  The leaf's equality test is true at `58`, so the
run takes `if.then173.i`. -/
theorem colStep₄ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "LeafBlock3")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58))) :
    WalkLink calls G C s { C with block := "if.then173.i" } (colS₄ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.LeafBlock3_at G C s hInv hblock h8
  have hbit : evalICmp .eq (BitVec.ofNat 8 58) (BitVec.ofNat 8 58) = 1 := by decide
  have hstate : s' = colS₄ s := hs'.trans (by simp [colS₄, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.then173.i` at depth zero.**  `%sp.i.0248 = 0` is true, so the run takes the
refusal store `if.then176.i`. -/
theorem colStep₅ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then173.i")
    (hsp : C.sp = 0) :
    WalkLink calls G C s { C with block := "if.then176.i" } (colS₅ s) := by
  have h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 0)) := by
    simpa only [evalOperand, hsp] using hInv.depth_reg
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then173_i_at G C s hInv hblock h1
  have hbit : evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = 1 := by decide
  have hstate : s' = colS₅ s := hs'.trans (by simp [colS₅, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.then176.i`.**  The refusal's offset store: the entry's position goes to
`%e + 8` and the edge is the refusal copy. -/
theorem colStep₆ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then176.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (colS₆ C j s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then176_i_at G C s hInv hblock hv he hj hj64
  rw [hs'] at hl
  exact hl

/-- **The colon's refusal, as one counted run.**  Six links from the head to
`if.then`. -/
theorem colonRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  have h8₁ : evalOperand (colS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (colS₂ (colS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (colS₃ (colS₂ (colS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₃, colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have hv₆ : evalOperand (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    simpa only [colS₅, colS₄, colS₃, colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%cmp174.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf4") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%idxprom.i") _ _ (by decide)] using hv
  have he₆ : lookupName (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))).env "%e" =
      some (.ptr C.stage.e) := by
    simpa only [colS₅, colS₄, colS₃, colS₂, colS₁, State.bind,
      lookupName_cons_ne (k := "%cmp174.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf4") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)] using he
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock5" } (colS₁ s) :=
    colStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock5" } (colS₁ s)
      { C with block := "NodeBlock" } (colS₂ (colS₁ s)) :=
    colStep₂ G { C with block := "NodeBlock5" } (colS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "NodeBlock" } (colS₂ (colS₁ s))
      { C with block := "LeafBlock3" } (colS₃ (colS₂ (colS₁ s))) :=
    colStep₃ G { C with block := "NodeBlock" } (colS₂ (colS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "LeafBlock3" } (colS₃ (colS₂ (colS₁ s)))
      { C with block := "if.then173.i" } (colS₄ (colS₃ (colS₂ (colS₁ s)))) :=
    colStep₄ G { C with block := "LeafBlock3" } (colS₃ (colS₂ (colS₁ s))) L₃.inv' rfl h8₃
  have L₅ : WalkLink calls G { C with block := "if.then173.i" }
      (colS₄ (colS₃ (colS₂ (colS₁ s)))) { C with block := "if.then176.i" }
      (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) :=
    colStep₅ G { C with block := "if.then173.i" } (colS₄ (colS₃ (colS₂ (colS₁ s))))
      L₄.inv' rfl hsp
  have L₆ : WalkLink calls G { C with block := "if.then176.i" }
      (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s)))))
      { C with block := "if.then", eoff := j, refusal := true }
      (colS₆ C j (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s)))))) :=
    colStep₆ G { C with block := "if.then176.i" }
      (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) L₅.inv' rfl hv₆ he₆ hj hj64
  refine ⟨{ C with block := "if.then", eoff := j, refusal := true },
    colS₆ C j (colS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))), 6, ?_, rfl,
    L₆.inv'.eoff_le, refusePrice_of_le G C (by omega) hk⟩
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
    (Seg.tail L₅ (Seg.tail L₆ (Seg.nil L₆.inv')))))))

/-- **The `refuse` witness at a depth-zero colon**, in the exact shape
`WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct.  Six
blocks from the head to the refusal copy, the entry's position as the offset, and the
price inside one entry's allowance — a refusal with entries still remaining. -/
theorem walkRefuseWitness_colon {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  colonRefuse_at G C s hInv hhead h8 hsp hv he hj hj64 hk

/-! ### The comma at depth zero

`%8 = 44` fails `NodeBlock5`'s pivot (its bit is `%8 < 44`), so the switch takes
`NodeBlock → LeafBlock1`, whose equality test at `44` reaches `if.then127.i`; a
depth-zero register there refuses through `if.then130.i`'s offset store.  Six blocks,
the same shape as the colon's, and a second early refusal with entries remaining.

The pivot chain also settles a branch *not* taken: `LeafBlock7` is only reached from
`NodeBlock11`, whose own pivot is `%8 < 93`, after `NodeBlock21`'s negated `%8 < 91` —
so the byte there is at least `91`, and its `44` test is clear.  `if.then.i` and
`if.then16.i` are therefore not enterable from the head at any byte the dispatch
carries; that absence is recorded here as a statement about the byte rather than as a
segment, since a refusal it cannot produce is not a witness. -/

/-- `NodeBlock21` at `%8 = 44`: `%8 < 91` is true, so the edge is `NodeBlock5`. -/
def comS₁ (s : State) : State :=
  { s.bind "%Pivot22" (.int 1 (1 : BitVec 1)) with pc := "NodeBlock5", pre := some s.pc }

/-- `NodeBlock5` at `%8 = 44`: `%8 < 44` is false, so the edge is `NodeBlock`. -/
def comS₂ (s : State) : State :=
  { s.bind "%Pivot6" (.int 1 (0 : BitVec 1)) with pc := "NodeBlock", pre := some s.pc }

/-- `NodeBlock` at `%8 = 44`: `%8 < 58` is true, so the edge is `LeafBlock1`. -/
def comS₃ (s : State) : State :=
  { s.bind "%Pivot" (.int 1 (1 : BitVec 1)) with pc := "LeafBlock1", pre := some s.pc }

/-- `LeafBlock1` at `%8 = 44`: `%8 = 44` is true, so the edge is `if.then127.i`. -/
def comS₄ (s : State) : State :=
  { s.bind "%SwitchLeaf2" (.int 1 (1 : BitVec 1)) with
    pc := "if.then127.i", pre := some s.pc }

/-- `if.then127.i` at a depth-zero register: the edge is `if.then130.i`. -/
def comS₅ (s : State) : State :=
  { s.bind "%cmp128.i" (.int 1 (1 : BitVec 1)) with pc := "if.then130.i", pre := some s.pc }

/-- `if.then130.i`: the entry's position written at `%e + 8`, at `if.then`. -/
def comS₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State) : State :=
  { { s with
      env := ("%off1.i.i66", .ptr (C.stage.e + 8)) :: s.env
      mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s.pc }

/-- **`NodeBlock21` at a comma.**  `%8 < 91` is true at `44`. -/
theorem comStep₁ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44))) :
    WalkLink calls G C s { C with block := "NodeBlock5" } (comS₁ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 44) (BitVec.ofNat 8 91) = 1 := by decide
  have hstate : s' = comS₁ s := hs'.trans (by simp [comS₁, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock5` at a comma.**  `%8 < 44` is false at `44`, so the edge is
`NodeBlock`. -/
theorem comStep₂ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock5")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44))) :
    WalkLink calls G C s { C with block := "NodeBlock" } (comS₂ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock5_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 44) (BitVec.ofNat 8 44) = 0 := by decide
  have hstate : s' = comS₂ s := hs'.trans (by simp [comS₂, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock` at a comma.**  `%8 < 58` is true at `44`, so the edge is
`LeafBlock1`. -/
theorem comStep₃ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44))) :
    WalkLink calls G C s { C with block := "LeafBlock1" } (comS₃ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 44) (BitVec.ofNat 8 58) = 1 := by decide
  have hstate : s' = comS₃ s := hs'.trans (by simp [comS₃, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`LeafBlock1` at a comma.**  The leaf's equality test is true at `44`, so the
run takes `if.then127.i`. -/
theorem comStep₄ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "LeafBlock1")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44))) :
    WalkLink calls G C s { C with block := "if.then127.i" } (comS₄ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.LeafBlock1_at G C s hInv hblock h8
  have hbit : evalICmp .eq (BitVec.ofNat 8 44) (BitVec.ofNat 8 44) = 1 := by decide
  have hstate : s' = comS₄ s := hs'.trans (by simp [comS₄, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.then127.i` at depth zero.**  `%sp.i.0248 = 0` is true, so the run takes the
refusal store `if.then130.i`. -/
theorem comStep₅ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then127.i")
    (hsp : C.sp = 0) :
    WalkLink calls G C s { C with block := "if.then130.i" } (comS₅ s) := by
  have h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 0)) := by
    simpa only [evalOperand, hsp] using hInv.depth_reg
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then127_i_at G C s hInv hblock h1
  have hbit : evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = 1 := by decide
  have hstate : s' = comS₅ s := hs'.trans (by simp [comS₅, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.then130.i`.**  The refusal's offset store: the entry's position goes to
`%e + 8` and the edge is the refusal copy. -/
theorem comStep₆ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then130.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (comS₆ C j s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then130_i_at G C s hInv hblock hv he hj hj64
  rw [hs'] at hl
  exact hl

/-- **The comma's refusal, as one counted run.**  Six links from the head to
`if.then`. -/
theorem commaRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  have h8₁ : evalOperand (comS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)) := by
    simpa only [comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (comS₂ (comS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 44)) := by
    simpa only [comS₂, comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (comS₃ (comS₂ (comS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 44)) := by
    simpa only [comS₃, comS₂, comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have hv₆ : evalOperand (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s))))) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    simpa only [comS₅, comS₄, comS₃, comS₂, comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%cmp128.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf2") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%idxprom.i") _ _ (by decide)] using hv
  have he₆ : lookupName (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s))))).env "%e" =
      some (.ptr C.stage.e) := by
    simpa only [comS₅, comS₄, comS₃, comS₂, comS₁, State.bind,
      lookupName_cons_ne (k := "%cmp128.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf2") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)] using he
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock5" } (comS₁ s) :=
    comStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock5" } (comS₁ s)
      { C with block := "NodeBlock" } (comS₂ (comS₁ s)) :=
    comStep₂ G { C with block := "NodeBlock5" } (comS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "NodeBlock" } (comS₂ (comS₁ s))
      { C with block := "LeafBlock1" } (comS₃ (comS₂ (comS₁ s))) :=
    comStep₃ G { C with block := "NodeBlock" } (comS₂ (comS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "LeafBlock1" } (comS₃ (comS₂ (comS₁ s)))
      { C with block := "if.then127.i" } (comS₄ (comS₃ (comS₂ (comS₁ s)))) :=
    comStep₄ G { C with block := "LeafBlock1" } (comS₃ (comS₂ (comS₁ s))) L₃.inv' rfl h8₃
  have L₅ : WalkLink calls G { C with block := "if.then127.i" }
      (comS₄ (comS₃ (comS₂ (comS₁ s)))) { C with block := "if.then130.i" }
      (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s))))) :=
    comStep₅ G { C with block := "if.then127.i" } (comS₄ (comS₃ (comS₂ (comS₁ s))))
      L₄.inv' rfl hsp
  have L₆ : WalkLink calls G { C with block := "if.then130.i" }
      (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s)))))
      { C with block := "if.then", eoff := j, refusal := true }
      (comS₆ C j (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s)))))) :=
    comStep₆ G { C with block := "if.then130.i" }
      (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s))))) L₅.inv' rfl hv₆ he₆ hj hj64
  refine ⟨{ C with block := "if.then", eoff := j, refusal := true },
    comS₆ C j (comS₅ (comS₄ (comS₃ (comS₂ (comS₁ s))))), 6, ?_, rfl,
    L₆.inv'.eoff_le, refusePrice_of_le G C (by omega) hk⟩
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
    (Seg.tail L₅ (Seg.tail L₆ (Seg.nil L₆.inv')))))))

/-- **The `refuse` witness at a depth-zero comma**, in the exact shape
`WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct. -/
theorem walkRefuseWitness_comma {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  commaRefuse_at G C s hInv hhead h8 hsp hv he hj hj64 hk

/-! ### The branches that are not witnesses: the four traps

Four blocks of the dispatch's reachable set are `@llvm.trap` arms —
`if.end.i83` (the arena's reserve), `if.end.i.i.i` and `if.end.i.i.i64` (the two event
reserves) and `if.end.i86` (the thirteen-byte record reserve).  `walkTrap_noStep` is
their verdict: `stage2Calls` answers `none` at the trapping call, so the block cannot
step at all.  A `refuse`/`finish` witness for them is therefore not owed, and cannot
exist: a link *is* a jump, so no link leaves a trap, and a dispatch's run — a chain of
links — cannot pass one.

What keeps the run out is the guard before each: `walkEventReserve_clear` and
`walkArenaReserve_clear` are the two clauses read at the invariant, and the thirteen-
byte reserve is the same arithmetic at the widest record.  Those are the statements the
four rows owe, and they are programmes of the invariant rather than witnesses of a
refusal. -/

/-- **No link leaves a trap block.**  A link's step is a jump and a trap's step is not,
so a run that reaches one stops there — which is what makes the four `unreachable` rows
obligations about their guards and not about a segment. -/
theorem walkNoLinkFromTrap {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {C' : WalkCarry G} {s' : State}
    (hpc : s.pc = "if.end.i83" ∨ s.pc = "if.end.i.i.i" ∨ s.pc = "if.end.i.i.i64" ∨
      s.pc = "if.end.i86") :
    ¬ WalkLink (stage2Calls stage2SubCalls) G C s C' s' := by
  intro hl
  exact walkTrap_noStep s hpc ⟨s', WalkLink.step hl⟩


/-- **A bit that is zero from a disequality.**  `evalICmp .eq` is `ofBool (x = y)`, so a
witness that the operands differ is the zero bit. -/
theorem refuseICmp_eq_zero {w : Nat} {x y : BitVec w} (h : x ≠ y) :
    evalICmp .eq x y = 0 := by
  simp [evalICmp, BitVec.ofBool, h]

/-! ### The stack marker's refusal

A colon at non-zero depth descends into the type stack: `if.end179.i` reads the marker
one below the depth and tests it against `1` (the brace), and a marker that is not `1`
is refused at `if.then192.i`.  The block is the layer's five-instruction marker class —
`walkStackMarkerStep` already names the successor — so this branch needs no
`denoteCode` of its own, unlike `if.end59.i`'s select nest. -/

/-- `if.then173.i` at a *non-zero* depth: the depth test's cell is zero, at
`if.end179.i`. -/
def smS₅ (s : State) : State :=
  { s.bind "%cmp174.i" (.int 1 (0 : BitVec 1)) with pc := "if.end179.i", pre := some s.pc }

/-- `if.end179.i`'s successor, at the environment its stack read binds. -/
abbrev smS₆ (s : State) (sp ct : Nat) (b : UInt8) : State :=
  { stateAt (walkMarkerEnv "%sub181.i" "%idxprom182.i" "%arrayidx183.i" "%23"
      "%cmp185.not.i" (BitVec.ofNat 32 sp) (BitVec.ofNat 32 4294967295) ct b.toNat
      (BitVec.ofNat 8 1) s.env) s with
    pc := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
      then "lor.lhs.false.i" else "if.then192.i")
    pre := some s.pc }

/-- `if.then192.i`: the entry's position written at `%e + 8`, at `if.then`. -/
def smS₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State) : State :=
  { { s with
      env := ("%off1.i.i74", .ptr (C.stage.e + 8)) :: s.env
      mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s.pc }

/-- **`if.then173.i` above depth zero.**  The depth register is not `0`, so the run takes
the type stack's check `if.end179.i`. -/
theorem smStep₅ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then173.i")
    (hsp : C.sp ≠ 0) :
    WalkLink calls G C s { C with block := "if.end179.i" } (smS₅ s) := by
  have hsp32 : C.sp < 2 ^ 32 := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h
    omega
  have h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 C.sp)) := by
    simpa only [evalOperand] using hInv.depth_reg
  have hne : BitVec.ofNat 32 C.sp ≠ BitVec.ofNat 32 0 := by
    intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt hsp32] at h'
    omega
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then173_i_at G C s hInv hblock h1
  have hbit : evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 0 :=
    refuseICmp_eq_zero hne
  have hstate : s' = smS₅ s := hs'.trans (by simp [smS₅, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.end179.i`'s target, named.**  The marker class's step (`walkStackMarkerStep`)
and the class's link, identified by `Ctrl.jump`'s injectivity. -/
theorem walkIfEnd179_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end179.i")
    {sp ct : Nat} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b]) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .eq (BitVec.ofNat 8 b.toNat)
            (BitVec.ofNat 8 1) = 1 then "lor.lhs.false.i" else "if.then192.i") } s' ∧
      s' = smS₆ s sp ct b := by
  obtain ⟨s', hl⟩ := WalkLink.if_end179_i (calls := calls) G C s hInv hblock hsp hct hq63 hread
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_end179_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_end179_i_find
  have hstep := walkStackMarkerStep (calls := calls) (s := s) (B := walkIf_end179_i)
    (gg := "%sub181.i") (zx := "%idxprom182.i") (ap := "%arrayidx183.i") (ld := "%23")
    (d := "%cmp185.not.i") (base := "%ctype.i") (tl := "lor.lhs.false.i")
    (fl := "if.then192.i") (x := BitVec.ofNat 32 sp)
    (c := BitVec.ofNat 32 4294967295) (a := ct) (one := BitVec.ofNat 8 1) (bs := [b])
    (q := b.toNat) hfind rfl rfl hsp hct (by decide) (by decide) hq63 hread
    (bytesToNat_singleton b) (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.end179.i` at a marker that is not the brace.**  The stack's byte disagrees with
`1`, so the run takes the refusal store. -/
theorem smStep₆ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end179.i")
    {sp ct : Nat} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b])
    (hbit : evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 0) :
    WalkLink calls G C s { C with block := "if.then192.i" } (smS₆ s sp ct b) := by
  obtain ⟨s', hl, hs'⟩ := walkIfEnd179_at (calls := calls) G C s hInv hblock hsp hct hq63 hread
  have hcond : ¬ (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1) := by
    rw [hbit]; decide
  rw [hs'] at hl
  rw [if_neg hcond] at hl
  exact hl

/-- **`if.then192.i`.**  The refusal's offset store: the entry's position goes to
`%e + 8` and the edge is the refusal copy. -/
theorem smStep₇ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then192.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (smS₇ C j s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then192_i_at G C s hInv hblock hv he hj hj64
  rw [hs'] at hl
  exact hl

/-- **The stack marker's refusal, as one counted run.**  Seven links: the switch's four
pivots at `:`, the depth test's non-refusal arm, the type stack's marker check, and the
offset store. -/
theorem stackMarkerRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) (hq1 : (C.tyMap (C.sp - 1)).toNat ≠ 1)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  have h8₁ : evalOperand (colS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (colS₂ (colS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (colS₃ (colS₂ (colS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₃, colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock5" } (colS₁ s) :=
    colStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock5" } (colS₁ s)
      { C with block := "NodeBlock" } (colS₂ (colS₁ s)) :=
    colStep₂ G { C with block := "NodeBlock5" } (colS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "NodeBlock" } (colS₂ (colS₁ s))
      { C with block := "LeafBlock3" } (colS₃ (colS₂ (colS₁ s))) :=
    colStep₃ G { C with block := "NodeBlock" } (colS₂ (colS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "LeafBlock3" } (colS₃ (colS₂ (colS₁ s)))
      { C with block := "if.then173.i" } (colS₄ (colS₃ (colS₂ (colS₁ s)))) :=
    colStep₄ G { C with block := "LeafBlock3" } (colS₃ (colS₂ (colS₁ s))) L₃.inv' rfl h8₃
  have L₅ : WalkLink calls G { C with block := "if.then173.i" }
      (colS₄ (colS₃ (colS₂ (colS₁ s)))) { C with block := "if.end179.i" }
      (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) :=
    smStep₅ G { C with block := "if.then173.i" } (colS₄ (colS₃ (colS₂ (colS₁ s))))
      L₄.inv' rfl hsp
  have hsp₆ : lookupName (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))).env "%sp.i.0248" =
      some (.int 32 (BitVec.ofNat 32 C.sp)) :=
    L₅.inv'.depth_reg
  have hct₆ : lookupName (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))).env "%ctype.i" =
      some (.ptr C.stage.ctype) :=
    L₅.inv'.ptrs.2.2.2.1
  have hsub : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hsp32 : C.sp < 2 ^ 32 := by
      have h := hInv.depth_cap
      simp only [stage2StackExtent] at h
      omega
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    have hb : (4294967295 : Nat) < 2 ^ 32 := by decide
    rw [Nat.mod_eq_of_lt hsp32, Nat.mod_eq_of_lt hb]
    have hsum : C.sp + 4294967295 = (C.sp - 1) + 4294967296 := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hq63 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63 := by
    rw [hsub]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    omega
  have hread : readBytes (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))).mem
      (C.stage.ctype + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [C.tyMap (C.sp - 1)] := by
    rw [hsub, JsonEntrySteps.readBytes_one]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    have hlt : C.sp - 1 < C.wlen := by
      have hspw : C.sp ≤ C.wlen := L₅.inv'.sp_le_wlen
      omega
    rw [L₅.inv'.tyBytes (C.sp - 1) hlt]
    rfl
  have hq256 : (C.tyMap (C.sp - 1)).toNat < 256 := UInt8.toNat_lt (C.tyMap (C.sp - 1))
  have hbit : evalICmp .eq (BitVec.ofNat 8 (C.tyMap (C.sp - 1)).toNat)
      (BitVec.ofNat 8 1) = 0 := by
    refine refuseICmp_eq_zero (fun h => hq1 ?_)
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq256,
      Nat.mod_eq_of_lt (by decide : (1 : Nat) < 256)] at h'
    exact h'
  have L₆ : WalkLink calls G { C with block := "if.end179.i" }
      (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) { C with block := "if.then192.i" }
      (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype
        (C.tyMap (C.sp - 1))) :=
    smStep₆ G { C with block := "if.end179.i" } (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s)))))
      L₅.inv' rfl hsp₆ hct₆ hq63 hread hbit
  have hv₇ : evalOperand (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype
      (C.tyMap (C.sp - 1))) (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)) := by
    simp only [smS₆, walkMarkerEnv, cells, stateAt, evalOperand,
      lookupName_cons_ne (k := "%cmp185.not.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%23") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%arrayidx183.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%idxprom182.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%sub181.i") (n := "%idxprom.i") _ _ (by decide),
      smS₅, colS₄, colS₃, colS₂, colS₁, State.bind,
      lookupName_cons_ne (k := "%cmp174.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf4") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%idxprom.i") _ _ (by decide)]
    exact hv
  have he₇ : lookupName (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp
      C.stage.ctype (C.tyMap (C.sp - 1))).env "%e" = some (.ptr C.stage.e) := by
    simp only [smS₆, walkMarkerEnv, cells, stateAt,
      lookupName_cons_ne (k := "%cmp185.not.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%23") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%arrayidx183.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%idxprom182.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%sub181.i") (n := "%e") _ _ (by decide),
      smS₅, colS₄, colS₃, colS₂, colS₁, State.bind,
      lookupName_cons_ne (k := "%cmp174.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf4") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)]
    exact he
  have L₇ : WalkLink calls G { C with block := "if.then192.i" }
      (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype
        (C.tyMap (C.sp - 1)))
      { C with block := "if.then", eoff := j, refusal := true }
      (smS₇ C j (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype
        (C.tyMap (C.sp - 1)))) :=
    smStep₇ G { C with block := "if.then192.i" }
      (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype
        (C.tyMap (C.sp - 1)))
      L₆.inv' rfl hv₇ he₇ hj hj64
  refine ⟨{ C with block := "if.then", eoff := j, refusal := true },
    smS₇ C j (smS₆ (smS₅ (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype
      (C.tyMap (C.sp - 1))), 7, ?_, rfl, L₇.inv'.eoff_le,
    refusePrice_of_le G C (by omega) hk⟩
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
    (Seg.tail L₅ (Seg.tail L₆ (Seg.tail L₇ (Seg.nil L₇.inv'))))))))

/-- **The `refuse` witness at a colon whose enclosing marker is not the brace**, in the
exact shape `WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct. -/
theorem walkRefuseWitness_stackMarker {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) (hq1 : (C.tyMap (C.sp - 1)).toNat ≠ 1)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  stackMarkerRefuse_at G C s hInv hhead h8 hsp hq1 hv he hj hj64 hk

/-! ### The mismatched literal

The container's nesting is *checked* at `if.end59.i`: the byte one below the depth is the
marker the type stack holds there, and a closing bracket that disagrees with it is the
refusal `if.then71.i`.  Its run is the dispatch's select nest, whose `denoteCode` is now
two four-instruction theorems with a named intermediate environment
(`walkSelectEnv4`), so naming its target is a two-line consumer rather than the
eight-instruction term this file's earlier attempt at it could not elaborate under the
cap.

`if.end59.i` is also the block the state-stack refusal (`cleanup104.i`) crosses, which is
why the naming is one statement and not two. -/

/-- The select nest's own cell, in the form `walkSelectEnv` binds it: the expected
marker compared with the byte's `zext`.  Writing the bit through this `abbrev` is what
makes the step's successor and the state named below the *same* term. -/
abbrev stackSelBit (db : BitVec 8) (b : UInt8) : BitVec 1 :=
  evalICmp .eq
    (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then (1 : BitVec 32) else (2 : BitVec 32))
    (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b])).toNat)

/-- The state `if.end59.i` leaves, at the environment its select nest binds. -/
abbrev stackSelOut (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8)
    (bit : BitVec 1) : State :=
  { stateAt (walkSelectEnv "%sub.i" "%cmp61.i" "%conv64.i" "%idxprom65.i" "%arrayidx66.i"
      "%14" "%conv67.i" "%cmp69.not.i" db (BitVec.ofNat 32 sp)
      (BitVec.ofNat 32 4294967295) ct (bytesToNat [b]) s.env) s with
    pc := (if bit = 1 then "if.end74.i" else "if.then71.i")
    pre := some s.pc }

/-- **`if.end59.i`'s target, named.**  The select class's step (`walkSelectStep`), at
the cells this branch reads: the depth register, the document byte, the type stack's
base, and the marker one below the depth. -/
theorem walkIfEnd59_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end59.i")
    {sp ct : Nat} {db : BitVec 8} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (h8 : lookupName s.env "%8" = some (.int 8 db))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b]) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .eq (walkSelVal db)
            (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b])).toNat) = 1
          then "if.end74.i" else "if.then71.i") } s' ∧
      s' = stackSelOut s sp ct db b (stackSelBit db b) := by
  obtain ⟨s', hl⟩ := WalkLink.if_end59_i (calls := calls) G C s hInv hblock hsp h8 hct hq63
    hread
  refine ⟨s', hl, ?_⟩
  have hbit : lookupName (stateAt (walkSelectEnv "%sub.i" "%cmp61.i" "%conv64.i"
      "%idxprom65.i" "%arrayidx66.i" "%14" "%conv67.i" "%cmp69.not.i" db
      (BitVec.ofNat 32 sp) (BitVec.ofNat 32 4294967295) ct (bytesToNat [b]) s.env) s).env
      "%cmp69.not.i" = some (.int 1 (stackSelBit db b)) := by
    simp only [stateAt, walkSelectEnv, cells, stackSelBit]
    simp [lookupName]
  have hstep := walkSelectStep (calls := calls) (s := s) (B := walkIf_end59_i)
    (sub := "%sub.i") (cmpi := "%cmp61.i") (sel := "%conv64.i") (zx := "%idxprom65.i")
    (apx := "%arrayidx66.i") (ldv := "%14") (cvt := "%conv67.i") (d := "%cmp69.not.i")
    (base := "%ctype.i") (tl := "if.end74.i") (fl := "if.then71.i")
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 4294967295) (ct := ct)
    (q := bytesToNat [b]) (bs := [b]) (db := db) (bit := stackSelBit db b)
    (by rw [hInv.pc_eq, hblock]; exact walkIf_end59_i_find) rfl rfl hsp h8 hct (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hq63 hread (bytesToNat_singleton b) hbit
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- `if.then53.i` at a *non-zero* depth: the depth test's cell is zero, at
`if.end59.i`. -/
def mlS₅ (s : State) : State :=
  { s.bind "%cmp54.i" (.int 1 (0 : BitVec 1)) with pc := "if.end59.i", pre := some s.pc }

/-- `if.then71.i`: the entry's position written at `%e + 8`, at `if.then`. -/
def mlS₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State) : State :=
  { { s with
      env := ("%off1.i.i43", .ptr (C.stage.e + 8)) :: s.env
      mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s.pc }

/-- **`if.then53.i` above depth zero.**  The depth register is not `0`, so the run takes
the nesting check `if.end59.i` instead of the refusal arm. -/
theorem mlStep₅ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then53.i")
    (hsp : C.sp ≠ 0) :
    WalkLink calls G C s { C with block := "if.end59.i" } (mlS₅ s) := by
  have hsp32 : C.sp < 2 ^ 32 := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h
    omega
  have h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 C.sp)) := by
    simpa only [evalOperand] using hInv.depth_reg
  have hne : BitVec.ofNat 32 C.sp ≠ BitVec.ofNat 32 0 := by
    intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt hsp32] at h'
    omega
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then53_i_at G C s hInv hblock h1
  have hbit : evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 0 :=
    refuseICmp_eq_zero hne
  have hstate : s' = mlS₅ s := hs'.trans (by simp [mlS₅, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`if.end59.i` at a disagreeing bracket.**  The document byte's bracket does not name
the marker the type stack holds, so the run takes the refusal store. -/
theorem mlStep₆ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end59.i")
    {sp ct : Nat} {db : BitVec 8} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (h8 : lookupName s.env "%8" = some (.int 8 db))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b])
    (hbit : evalICmp .eq (walkSelVal db)
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b])).toNat) = 0) :
    WalkLink calls G C s { C with block := "if.then71.i" }
      (stackSelOut s sp ct db b (stackSelBit db b)) := by
  obtain ⟨s', hl, hs'⟩ := walkIfEnd59_at (calls := calls) G C s hInv hblock hsp h8 hct hq63
    hread
  have hcond : ¬ (evalICmp .eq (walkSelVal db)
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b])).toNat) = 1) := by
    rw [hbit]; decide
  rw [hs'] at hl
  rw [if_neg hcond] at hl
  exact hl

/-- **`if.then71.i`.**  The refusal's offset store: the entry's position goes to
`%e + 8` and the edge is the refusal copy. -/
theorem mlStep₇ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then71.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (mlS₇ C j s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.if_then71_i_at G C s hInv hblock hv he hj hj64
  rw [hs'] at hl
  exact hl

/-- **The mismatched literal, as one counted run.**  Seven links: the switch's four
pivots at `]`, the depth test's *non*-refusal arm, the select nest that compares the
bracket with the type stack's marker, and the offset store. -/
theorem mismatchedRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp ≠ 0) (hq : (C.tyMap (C.sp - 1)).toNat ≠ 2)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
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
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock19" } (refuseS₁ s) :=
    refuseStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock19" } (refuseS₁ s)
      { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s)) :=
    refuseStep₂ G { C with block := "NodeBlock19" } (refuseS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s))
      { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s))) :=
    refuseStep₃ G { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "LeafBlock9" }
      (refuseS₃ (refuseS₂ (refuseS₁ s))) { C with block := "if.then53.i" }
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) :=
    refuseStep₄ G { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s)))
      L₃.inv' rfl h8₃
  have L₅ : WalkLink calls G { C with block := "if.then53.i" }
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) { C with block := "if.end59.i" }
      (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) :=
    mlStep₅ G { C with block := "if.then53.i" } (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))
      L₄.inv' rfl hsp
  have hsp₆ : lookupName (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))).env
      "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 C.sp)) :=
    L₅.inv'.depth_reg
  have h8₆ : lookupName (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))).env "%8" =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [mlS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf10") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have hct₆ : lookupName (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))).env
      "%ctype.i" = some (.ptr C.stage.ctype) :=
    L₅.inv'.ptrs.2.2.2.1
  have hsub : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hsp32 : C.sp < 2 ^ 32 := by
      have h := hInv.depth_cap
      simp only [stage2StackExtent] at h
      omega
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    have hb : (4294967295 : Nat) < 2 ^ 32 := by decide
    rw [Nat.mod_eq_of_lt hsp32, Nat.mod_eq_of_lt hb]
    rw [show C.sp + 4294967295 = (C.sp - 1) + 4294967296 from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hq63 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63 := by
    rw [hsub]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    omega
  have hread : readBytes (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))).mem
      (C.stage.ctype + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [C.tyMap (C.sp - 1)] := by
    rw [hsub, JsonEntrySteps.readBytes_one]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    have hlt : C.sp - 1 < C.wlen := by
      have hspw : C.sp ≤ C.wlen := L₅.inv'.sp_le_wlen
      omega
    rw [L₅.inv'.tyBytes (C.sp - 1) hlt]
    rfl
  have hq256 : (C.tyMap (C.sp - 1)).toNat < 256 := UInt8.toNat_lt (C.tyMap (C.sp - 1))
  have hbit : evalICmp .eq (walkSelVal (BitVec.ofNat 8 93))
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [C.tyMap (C.sp - 1)])).toNat) = 0 := by
    have hselbit : evalICmp .eq (BitVec.ofNat 8 93) (BitVec.ofNat 8 125) = 0 := by decide
    have hsel : walkSelVal (BitVec.ofNat 8 93) = BitVec.ofNat 32 2 := by
      rw [walkSelVal, walkSelBit, hselbit]
      rfl
    have hbs : bytesToNat [C.tyMap (C.sp - 1)] = (C.tyMap (C.sp - 1)).toNat := by
      simp [bytesToNat]
    have hq8 : (BitVec.ofNat 8 (C.tyMap (C.sp - 1)).toNat).toNat =
        (C.tyMap (C.sp - 1)).toNat := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hq256
    rw [hsel, hbs, hq8]
    refine refuseICmp_eq_zero (fun h => hq ?_)
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (2 : Nat) < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (C.tyMap (C.sp - 1)).toNat < 2 ^ 32)] at h'
    exact h'.symm
  have L₆ : WalkLink calls G { C with block := "if.end59.i" }
      (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) { C with block := "if.then71.i" }
      (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) C.sp
        C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
        (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1)))) :=
    mlStep₆ G { C with block := "if.end59.i" } (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))))
      L₅.inv' rfl hsp₆ h8₆ hct₆ hq63 hread hbit
  have hv₇ : evalOperand (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))))
      C.sp C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
      (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1)))) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    simp only [stackSelOut, stackSelBit, walkSelectEnv, cells, stateAt, evalOperand,
      lookupName_cons_ne (k := "%cmp69.not.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%conv67.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%14") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%arrayidx66.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%idxprom65.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%conv64.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%cmp61.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%sub.i") (n := "%idxprom.i") _ _ (by decide),
      mlS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, State.bind,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf10") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot12") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%idxprom.i") _ _ (by decide)]
    exact hv
  have he₇ : lookupName (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))))
      C.sp C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
      (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1)))).env "%e" =
      some (.ptr C.stage.e) := by
    simp only [stackSelOut, stackSelBit, walkSelectEnv, cells, stateAt,
      lookupName_cons_ne (k := "%cmp69.not.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%conv67.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%14") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%arrayidx66.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%idxprom65.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%conv64.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%cmp61.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%sub.i") (n := "%e") _ _ (by decide),
      mlS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, State.bind,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf10") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot12") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)]
    exact he
  have L₇ : WalkLink calls G { C with block := "if.then71.i" }
      (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) C.sp
        C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
        (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))))
      { C with block := "if.then", eoff := j, refusal := true }
      (mlS₇ C j (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) C.sp
        C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
        (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))))) :=
    mlStep₇ G { C with block := "if.then71.i" }
      (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) C.sp
        C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
        (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))))
      L₆.inv' rfl hv₇ he₇ hj hj64
  refine ⟨{ C with block := "if.then", eoff := j, refusal := true },
    mlS₇ C j (stackSelOut (mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))) C.sp
      C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
      (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1)))), 7, ?_, rfl,
    L₇.inv'.eoff_le, refusePrice_of_le G C (by omega) hk⟩
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
    (Seg.tail L₅ (Seg.tail L₆ (Seg.tail L₇ (Seg.nil L₇.inv'))))))))

/-- **The `refuse` witness at a mismatched bracket**, in the exact shape
`WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct: a closing
bracket inside a container whose marker it does not match, refused at the nesting check,
with the entry's position as the offset. -/
theorem walkRefuseWitness_mismatched {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp ≠ 0) (hq : (C.tyMap (C.sp - 1)).toNat ≠ 2)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  mismatchedRefuse_at G C s hInv hhead h8 hsp hq hv he hj hj64 hk

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.refusePrice_of_le
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₁
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₂
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₃
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₄
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₅
#print axioms LeanLLVM.Refinement.WalkScope.refuseStep₆
#print axioms LeanLLVM.Refinement.WalkScope.bracketRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_bracket
#print axioms LeanLLVM.Refinement.WalkScope.refuseUlt_zero
#print axioms LeanLLVM.Refinement.WalkScope.quoteRefuseStep₁
#print axioms LeanLLVM.Refinement.WalkScope.quoteRefuseStep₂
#print axioms LeanLLVM.Refinement.WalkScope.quoteRefuseStep₃
#print axioms LeanLLVM.Refinement.WalkScope.quoteRefuseStep₄
#print axioms LeanLLVM.Refinement.WalkScope.quoteRefuseStep₅
#print axioms LeanLLVM.Refinement.WalkScope.quoteRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_quote
#print axioms LeanLLVM.Refinement.WalkScope.colonRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_colon
#print axioms LeanLLVM.Refinement.WalkScope.commaRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_comma
#print axioms LeanLLVM.Refinement.WalkScope.walkNoLinkFromTrap
#print axioms LeanLLVM.Refinement.WalkScope.walkIfEnd179_at
#print axioms LeanLLVM.Refinement.WalkScope.smStep₅
#print axioms LeanLLVM.Refinement.WalkScope.smStep₆
#print axioms LeanLLVM.Refinement.WalkScope.smStep₇
#print axioms LeanLLVM.Refinement.WalkScope.stackMarkerRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_stackMarker
#print axioms LeanLLVM.Refinement.WalkScope.walkIfEnd59_at
#print axioms LeanLLVM.Refinement.WalkScope.mlStep₅
#print axioms LeanLLVM.Refinement.WalkScope.mlStep₆
#print axioms LeanLLVM.Refinement.WalkScope.mlStep₇
#print axioms LeanLLVM.Refinement.WalkScope.mismatchedRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_mismatched
