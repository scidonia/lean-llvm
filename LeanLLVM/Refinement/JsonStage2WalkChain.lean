/-
The walk's dispatch chain: the finite pieces of a revolution.

`WalkDispatch`'s interior is not one path.  A revolution is a finite path from the
loop head (`NodeBlock21`) to a scan's latch, one induction per scan over its counter,
and the token's post-scan blocks to the merge; `WalkSegment.trans` composes the three
and `WalkChain.append` the finite ones.  This module is the finite layer: `WalkChain`s
whose every carry and state is the one the step instances name
(`JsonStage2WalkSteps`), so a chain is `WalkChain.tail` at those terms and nothing is
re-derived.

A token class fixes the comparison bits, and the bits are what resolve each step's
`if`-shaped `pc`: the instances state their targets with the arm as an `if` on the
instruction's bit, and a class is the case that takes one arm at each branch.  So the
chains are stated per class, and the class is the hypothesis (`hlt`, `hge`, …) rather
than a branch inside the chain.

**A path's terminus is not one of its links.**  The head path ends at the first
latch, `while.body370.i`, and the latch is the *entry* of the scan — a `phi` over the
counter — so no step of its own is owed: the path's last link is the block that jumps
to it (`LeafBlock43_at`), whose target is exactly the latch.  So the head path's
missing set is three instances, not four: `cond.end349.i` (F, the call), and
`land.lhs.true357.i` and `land.rhs.i` (a single-block G sequence and an E block whose
body is a `gep` + `load`), with `LeafBlock33`, `land.rhs.i.preheader` and
`LeafBlock43` already named.

**The interface the chain runs on.**  Two facts hold at every link and are inherited
by every path.  A link's operand fact at the next state is the previous one *peeled*:
the step binds one cell, so `evalOperand` at the target is the source's fact after
`lookupName_cons_ne` at the bound name.  And a link's target carries
`pre := some (source.pc)`, so the next step's predecessor is the *previous target's*
`pc` (the block it came from), not the original head's — which is why a chain names
its intermediate states rather than a flat `s.pc`.

**Two facts that only appear at composition.**  The chain's selection is
`stage2Calls stage2SubCalls` by construction: the class-F instance is fixed at it (the
`lifetime.start` marker is the reference selection's own answer), so no chain
polymorphic in `calls` can compose it — the same reason `WalkPremises` pinned the
selection.  And a link's carry is the *nested* update
`{{C with block := b₁} with block := b₂}`, not the flattened `{C with block := b₂}`:
the two are definitionally equal, but only the nested form typechecks against the
link's own conclusion, so a chain follows the links' shapes rather than a tidied
version of them.

**What the chain's hypotheses cost.**  Every fact a link needs is one of three kinds.
The staging's registers are the invariant's (`WalkInv.regs` over `walkStaticRegs`,
which includes `%invariant.gep` as `G.b - 1` and the four stack slots); the cells a
step binds are its own `cells` list; and the *document's* bytes a scan loads are
`WalkGeom.doc` at the position `WalkInv.iter`'s lane names — a derivation from two
fields rather than a new one.  So no link has yet needed a carry field the model lacks;
if one does, that is a finding at the model, not a hypothesis at the chain.

**Per-link checklist, from the links that were written.**  Five things a chain
extension has to get right, each of which cost a rewrite when it was missed.  Keep the
chain at its state *def* and state the next link's facts at the def — `simp only
[headS₅, condEnd349OutAt, cells]` — rather than rewriting the def away with `rw`, which
turns every later fact into a statement about the raw nest.  `WalkInv.regs` takes a
*pair* and a membership proof, not a name: `hInv.regs ("%invariant.gep", .ptr (G.b - 1))
(by simp [walkStaticRegs])`.  A cell a step bound at a `Nat` is a `BitVec` in the
statement, so `%cond350.i`'s offset hypothesis is `c.toNat < 2 ^ 63` and the address
`(G.b - 1) + c.toNat` is `G.b + (c.toNat - 1)` only with `1 ≤ c.toNat` in hand — the
rewrite should `obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero …` rather than ask
`omega` for a subtraction it does not have.  And a link lemma fixed at one selection
(the class-F instance) fixes the whole chain's `calls`, which is why the chains here are
stated at `stage2Calls stage2SubCalls` and nowhere else.  And a successor state reached
through a branch arm still has the *unresolved* arm in its carry's `block`, so the
extension must resolve it first — `rw [show (if evalICmp .ugt c ix = 1 then "a" else "b")
= "a" from by simp [hugt]] at hchain` — otherwise the next link's `block` hypothesis
cannot be `rfl` and the invariant is at a carry whose `block` is an `if`.

**The rest of the chain has its steps.**  Every remaining step of the head chain
already exists as a named target in `WalkLink` — `NodeBlock41_at`, `LeafBlock33_at`,
`land_rhs_i_preheader_at`, `land_rhs_i_at`, `NodeBlock52_at`, `LeafBlock43_at` — so the
rest is composition: resolve each arm, supply each step's cell, and append.  A step's
named state is read off that step's own conclusion, which is why no further hypothesis
about the tail is needed.

**The target terms are part of the work.**  Each instance's state is a literal nest
(`{ (s.bind a v).bind b w with … }`), so a chain's target is that nest applied k
times and its statement grows with the path — at twenty-two blocks it is unreadable,
and its `simp` goals are about the nest rather than the program.  A long path is
therefore written the way the shapes already are: each intermediate state takes a
`def` (the role `walkMarkerEnv` plays for a block), the chain states those defs, and
the instance lemmas bridge one def to the next.  The two lemmas below are the same
chain at both lengths — one link with the literal form, two links with the recursion
made explicit — which is where the literal form stops paying.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkSteps
import LeanLLVM.Refinement.JsonStage2WalkStepsPath

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The chain, from the head

The dispatch's interior is not one path: a revolution is a finite path from the head
to a scan's latch, one induction per scan over its counter, and the token's
post-scan blocks to the merge.  These are the finite pieces, as `WalkChain`s, with
every carry and state the instances' own conclusions name — so a chain is
`WalkChain.tail` at those terms and nothing is re-derived.

A token class fixes the bits, and the bits are what resolve each step's `if`-shaped
`pc`.  The first piece is the head's opening comparison at the class whose first byte
is below `91`: `%Pivot22 = %8 < 91` is one, so the edge is `NodeBlock5` and the target
is the instance's state with that arm taken. -/
theorem walkHeadChain_lt91 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt : evalICmp .slt x (BitVec.ofNat 8 91) = 1) :
    ∃ (C₁ : WalkCarry G) (s₁ : State), WalkChain calls G C s C₁ s₁ ∧
      C₁ = { C with block := "NodeBlock5" } ∧
      s₁ = { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
        pc := "NodeBlock5", pre := some s.pc } := by
  obtain ⟨s₁, hlink, hs₁⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  refine ⟨_, s₁, WalkChain.tail hlink (WalkChain.nil hlink.inv'), ?_, ?_⟩
  · simp [hlt]
  · exact hs₁.trans (by simp [hlt])


/-- **The head's first two links.**  The switch's opening pivots on the first byte:
`%8 < 91` takes `NodeBlock5`, and there `%8 < 44` takes `LeafBlock`.  Two links, the
second at the state the first names — which is the whole threading question, and its
answer is the instances' own terms: the second reaches `%8` through the cell the first
bound, so its operand fact is the first's peeled past `%Pivot22`. -/
theorem walkHeadChain_lt91_lt44 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (hlt44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1) :
    ∃ (C₂ : WalkCarry G) (s₂ : State), WalkChain calls G C s C₂ s₂ ∧
      C₂ = { C with block := "LeafBlock" } ∧
      s₂ = { ({ (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
          pc := "NodeBlock5", pre := some s.pc }).bind
          "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
        pc := "LeafBlock"
        pre := some "NodeBlock5" } := by
  obtain ⟨C₁, s₁, hchain₁, rfl, rfl⟩ := walkHeadChain_lt91 hInv hhead h8 hlt91
  have h8' : evalOperand
      { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
        pc := "NodeBlock5", pre := some s.pc } (.reg "%8") = some (.int 8 x) := by
    simpa only [evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  obtain ⟨s₂, hlink₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at G _ _ (WalkChain.inv_last hchain₁) rfl h8'
  refine ⟨_, s₂, hchain₁.append (WalkChain.tail hlink₂ (WalkChain.nil hlink₂.inv')), ?_, ?_⟩
  · simp [hlt44]
  · exact hs₂.trans (by simp [hlt44])
/-- The head path's first three intermediate states, as `def`s: the environment each
step's binds leave, at the edge the class takes.  They are the *literal* terms the
instances name — a `def` and no more — so an instance's state equality applies by
`rfl` and the chain never carries the nest in its own statement. -/
def headS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock5", pre := some s.pc }

/-- The state `NodeBlock5` leaves: the second pivot's cell, at `LeafBlock`. -/
def headS₂ (s : State) (x : BitVec 8) : State :=
  { (headS₁ s x).bind "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
    pc := "LeafBlock", pre := some (headS₁ s x).pc }

/-- The state `LeafBlock` leaves on the non-quote arm: the quote test's cell, at
`sw.default.i`. -/
def headS₃ (s : State) (x : BitVec 8) : State :=
  { (headS₂ s x).bind "%SwitchLeaf"
      (.int 1 (evalICmp .eq x (BitVec.ofNat 8 34))) with
    pc := "sw.default.i", pre := some (headS₂ s x).pc }

/-- **The head path to `sw.default.i`, as a chain.**  Three links of the switch's
pivots at the class that takes `%8 < 91`, then `%8 < 44`, then `%8 ≠ 34`; the states
are the `def`s, so the statement names them instead of the nest. -/
theorem walkHeadChain_default {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (hlt44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0) :
    WalkChain calls G C s { C with block := "sw.default.i" } (headS₃ s x) := by
  -- the three operand facts, each the previous one peeled past the step's cell
  have h8₁ : evalOperand (headS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₂ : evalOperand (headS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headS₂, headS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  -- the first link, its carry and target resolved by the class's bit
  obtain ⟨s₁, hl₁, hs₁⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  have hl₁' : WalkLink calls G C s { C with block := "NodeBlock5" } (headS₁ s x) := by
    have : s₁ = headS₁ s x := by simpa [headS₁, hlt91] using hs₁
    rw [this] at hl₁
    simpa [hlt91] using hl₁
  -- the second
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at G _ _ hl₁'.inv' rfl h8₁
  have hl₂' : WalkLink calls G { C with block := "NodeBlock5" } (headS₁ s x)
      { C with block := "LeafBlock" } (headS₂ s x) := by
    have : s₂ = headS₂ s x := by simpa [headS₂, hlt44] using hs₂
    rw [this] at hl₂
    simpa [hlt44] using hl₂
  -- the third
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock_at G _ _ hl₂'.inv' rfl h8₂
  have hl₃' : WalkLink calls G { C with block := "LeafBlock" } (headS₂ s x)
      { C with block := "sw.default.i" } (headS₃ s x) := by
    have : s₃ = headS₃ s x := by simpa [headS₃, hne34] using hs₃
    rw [this] at hl₃
    simpa [hne34] using hl₃
  exact WalkChain.tail hl₁' (WalkChain.tail hl₂' (WalkChain.tail hl₃' (WalkChain.nil hl₃'.inv')))

/-- The state `sw.default.i` leaves on the arm that reaches `cond.end349.i`: the entry
count's test's cell. -/
def headS₄ (s : State) (x : BitVec 8) (inc nep : BitVec 64) : State :=
  { (headS₃ s x).bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep)) with
    pc := "cond.end349.i", pre := some (headS₃ s x).pc }

/-- **The head path to `cond.end349.i`'s successor.**  Two more links past the default
arm: the entry count's test at `sw.default.i`, then class F's own run at
`cond.end349.i` — whose successor is `condEnd349OutAt`, so the chain names it.

The two facts the pair needs are the count's word (`%nep`, the ABI's fourth argument)
and `%inc.i`, the header's increment; both are the caller's to supply, which is where a
token class's case split enters. -/
theorem walkHeadChain_to_condOut {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (hlt44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    {inc nep : BitVec 64} {c ix : BitVec 64} {reg p : String}
    (hinc : evalOperand (headS₃ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headS₃ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    (hpre4 : (headS₄ s x inc nep).pre = some "sw.default.i")
    (hinc4 : phiIncoming "sw.default.i" [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav4 : lookupName (headS₄ s x inc nep).env reg = some (.int 64 c))
    (hidx4 : lookupName (headS₄ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok4 : lookupName (headS₄ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap4 : lookupName (headS₄ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    ∃ (C₅ : WalkCarry G) (s₅ : State), WalkChain (stage2Calls stage2SubCalls) G C s C₅ s₅ ∧
      C₅ = { { C with block := "cond.end349.i" } with
        block := (if evalICmp .ugt c ix = 1
          then "land.lhs.true357.i" else "if.end372.i") } ∧
      s₅ = condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20) := by
  -- the first three links, at their own target
  have hchain₃ : WalkChain (stage2Calls stage2SubCalls) G C s
      { C with block := "sw.default.i" } (headS₃ s x) :=
    walkHeadChain_default (calls := stage2Calls stage2SubCalls) hInv hhead h8 hlt91 hlt44 hne34
  -- the default arm's test
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.sw_default_i_at G _ _ (WalkChain.inv_last hchain₃) rfl hinc hnep
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G
      { C with block := "sw.default.i" } (headS₃ s x)
      { C with block := "cond.end349.i" } (headS₄ s x inc nep) := by
    have : s₄ = headS₄ s x inc nep := hs₄.trans (by simp [headS₄, hge])
    rw [this] at hl₄
    simpa [hge] using hl₄
  -- class F's run
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.cond_end349_i_at G _ _ hl₄'.inv' rfl hpre4 hinc4 hav4 hidx4 htok4 hgap4
  refine ⟨_, s₅, hchain₃.append (WalkChain.tail hl₄' (WalkChain.tail hl₅ (WalkChain.nil hl₅.inv'))),
    rfl, hs₅⟩

/-- **The head path through the token's own byte to `NodeBlock41`.**  The arm that reached
`cond.end349.i`'s successor is resolved first, so the next link's block hypothesis is a
literal.  `%invariant.gep` is `G.b - 1` and `%cond350.i` the position, so the address is
the document's `position - 1`-th byte, read by `walkDoc_byte` — the byte is `G.bs.getD`'s,
not a hypothesis.  With `c.toNat = q + 1` the address normalises to `G.b + q`. -/
theorem walkHeadChain_to_nodeBlock41 {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (hlt44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    {inc nep c ix : BitVec 64} {reg : String}
    (hinc : evalOperand (headS₃ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headS₃ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0) (hugt : evalICmp .ugt c ix = 1)
    (hpre4 : (headS₄ s x inc nep).pre = some "sw.default.i")
    (hinc4 : phiIncoming "sw.default.i" [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav4 : lookupName (headS₄ s x inc nep).env reg = some (.int 64 c))
    (hidx4 : lookupName (headS₄ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok4 : lookupName (headS₄ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap4 : lookupName (headS₄ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    {q : Nat} (hpos : c.toNat = q + 1) (hq63 : c.toNat < 2 ^ 63) (hqn : q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap) :
    ∃ (C₆ : WalkCarry G) (s₆ : State), WalkChain (stage2Calls stage2SubCalls) G C s C₆ s₆ ∧
      C₆ = { { C with block := "cond.end349.i" } with block := "NodeBlock41" } ∧
      s₆ = { stateAt (cells [("%35", .int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)),
          ("%gep", .ptr ((G.b - 1) + c.toNat))]
          (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)).env)
          (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)) with
        pc := "NodeBlock41"
        pre := some (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok
          (C.stage.tok + 20)).pc } := by
  obtain ⟨C₅, s₅, hchain₅, hC₅, hs₅⟩ :=
    walkHeadChain_to_condOut (p := "sw.default.i") hInv hhead h8 hlt91 hlt44 hne34 hinc
      hnep hge hpre4 hinc4 hav4 hidx4 htok4 hgap4
  rw [hC₅] at hchain₅
  rw [hs₅] at hchain₅
  rw [show (if evalICmp .ugt c ix = 1 then "land.lhs.true357.i" else "if.end372.i")
    = "land.lhs.true357.i" from by simp [hugt]] at hchain₅
  have hInv₅ := WalkChain.inv_last hchain₅
  have hig : lookupName (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok
      (C.stage.tok + 20)).env "%invariant.gep" = some (.ptr (G.b - 1)) :=
    hInv₅.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok
      (C.stage.tok + 20)).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 c.toNat)) := by
    simp only [condEnd349OutAt, cells]
    rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
    rw [lookupName_cons_self, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbyte : readBytes (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok
      (C.stage.tok + 20)).mem ((G.b - 1) + c.toNat) 1 = some [G.bs.getD q 0] := by
    have hbpos : 0 < G.b := G.bPos
    rw [hpos, show G.b - 1 + (q + 1) = G.b + q from by omega]
    exact walkDoc_byte G _ _ hInv₅ halen hevlen hqn
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.land_lhs_true357_i_at G _ _ hInv₅ rfl hig hcond (by omega) hbyte
  refine ⟨_, s₆, hchain₅.append (WalkChain.tail hl₆ (WalkChain.nil hl₆.inv')), ?_, hs₆⟩
  rfl

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_lt91
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_lt91_lt44
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_default
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_to_condOut
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_to_nodeBlock41

end WalkScope

end LeanLLVM.Refinement
