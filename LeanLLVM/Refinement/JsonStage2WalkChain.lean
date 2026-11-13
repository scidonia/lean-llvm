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

**State the target with the nesting the links produce.**  `rfl` compares the literal, so
a chain lemma's `C₇` must be written `{ { { C with block := "a" } with block := "b" } with
block := "c" }` — each link's own step — and not a tidied version.  The same holds for a
step's named state: the helper's `s'` is a `bind`-under-`let` term, so re-typing it in a
different-but-equal form fails `rfl` even though the state agrees, and the extension should
pass the helper's own equality rather than restate it.

**The rest of the chain has its steps.**  Every remaining step of the head chain
already exists as a named target in `WalkLink` — `NodeBlock41_at`, `LeafBlock33_at`,
`land_rhs_i_preheader_at`, `land_rhs_i_at`, `NodeBlock52_at`, `LeafBlock43_at` — so the
rest is composition: resolve each arm, supply each step's cell, and append.  A step's
named state is read off that step's own conclusion, which is why no further hypothesis
about the tail is needed.  The tail is now composed: `walkChain_extend_leafBlock33`
through `walkChain_extend_leafBlock43` are one extension per step and
`walkScanChain_to_latch` is the five of them as one chain, to the scan's latch; the head
path's own last links are `walkHeadChain_to_nodeBlock41Out`'s, and
`walkHeadChain_to_scanLatch` is the twelve of them as one chain from the loop head to
the latch.  What that leaves is not a link but the repeated visit: an induction per
scan, which `WalkScanInduction` names.

**A chain's index wants a `def`, its states included.**  A `WalkChain`'s carry and state
are indices, and an index is unified syntactically: two terms that are definitionally
equal are not thereby the same index.  The elaborator unfolds an `abbrev` eagerly, so the
index it produces and the one written down differ as terms even when they agree, and the
composition fails at `exact`.  A `def` is not unfolded, so the produced index is the `def`
applied on both sides — which is why every carry and every intermediate state a chain
passes through is a `def` here (`scanCarryLeafBlock46`, `scanNodeBlock50In`, …), and why a
composition's statement names the state the run visits rather than one equal to it.

**Two more shapes a proof of these costs.**  A `WalkLocal`'s *state* argument must be
passed explicitly — left implicit, `rw` instantiates it by unification and leaves the
equality of the two state forms as a goal instead of the local fact.  And a leaf helper's
target state is the `stateAt`-form while the block's own state is the `bind`-form: they
are equal, but `simp only` will not close a *state* equality by definitional equality, so
the proof needs an explicit `rfl` after it and the abbreviation naming the state must
mirror the helper's form.

**Two shapes a resolved arm costs, beyond the nesting rule.**  `rfl` does not fire on
`if c then a else b` for a symbolic `c`, and neither does `simp [h]` when `h : c` — the
rewrite is one congruence away from the term it has to reach, so `simp` splits the `if`
instead and asks for `c` at a goal the hypothesis does not close.  `if_pos h` (and
`if_neg`, with `1 ≠ 0` on the one-bit comparison) is the form that applies: it is the
`if`'s own equation, so the arm is the literal the next link's `rfl` needs.  And a
`WalkLocal` premise that reads `C.inner` from a carry the chain has already nested does
not unify with the source carry's projection, however equal the two are — the fix is to
take the scan's bound as its own `Nat` parameter with `C.inner = inner`, so the
premise's term never contains the nested projection.

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

/-- The state `NodeBlock41` leaves at the class that takes `%35 < 13`: the pivot's
cell, at `LeafBlock33`. -/
def nodeBlock41OutAt (s : State) (b : BitVec 8) : State :=
  { (s.bind "%Pivot42" (.int 1 (evalICmp .slt b (BitVec.ofNat 8 13)))) with
    pc := "LeafBlock33", pre := some s.pc }

/-- **The head path through `NodeBlock41` to `LeafBlock33`.**  The cell it branches on is
the one `land.lhs.true357.i` bound, read at the successor's state — so the pivot's own
register fact is a lookup at the environment the previous link installed, and the step
is `NodeBlock41_at` with its arm resolved by the class's bit.  Its successor is named by
the `def` rather than by the nest, so the statement stays about the program. -/
theorem walkHeadChain_to_nodeBlock41Out {m0 : Mem} {G : WalkGeom m0}
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
    (hevlen : C.evlen ≤ G.evcap)
    (hbit : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD q 0).toNat)
      (BitVec.ofNat 8 13) = 1) :
    ∃ (C₇ : WalkCarry G) (s₇ : State), WalkChain (stage2Calls stage2SubCalls) G C s C₇ s₇ ∧
      C₇.block = "LeafBlock33" ∧
      lookupName s₇.env "%35" =
        some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)) := by
  obtain ⟨C₆, s₆, hchain₆, hC₆, hs₆⟩ :=
    walkHeadChain_to_nodeBlock41 hInv hhead h8 hlt91 hlt44 hne34 hinc hnep hge hugt hpre4
      hinc4 hav4 hidx4 htok4 hgap4 hpos hq63 hqn halen hevlen
  rw [hC₆] at hchain₆
  have hInv₆ := WalkChain.inv_last hchain₆
  -- the pivot's operand is the cell the previous link bound
  have h35 : evalOperand s₆ (.reg "%35") =
      some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)) := by
    rw [hs₆]
    show lookupName (cells
      [("%35", .int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)),
       ("%gep", .ptr ((G.b - 1) + c.toNat))]
      (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)).env)
      "%35" = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
    block_lk
  -- the step, its arm resolved by the class's bit
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G _ _ hInv₆ rfl h35
  have hres : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD q 0).toNat)
      (BitVec.ofNat 8 13) = 1 then "LeafBlock33" else "NodeBlock39")
      = "LeafBlock33" := if_pos hbit
  have hstep7 : s₇ = nodeBlock41OutAt s₆ (BitVec.ofNat 8 (G.bs.getD q 0).toNat) := by
    rw [hs₇]
    simp only [nodeBlock41OutAt, hres]
  rw [hstep7] at hl₇
  rw [hres] at hl₇
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G
      { { C with block := "cond.end349.i" } with block := "NodeBlock41" } s₆
      { { { C with block := "cond.end349.i" } with block := "NodeBlock41" } with
        block := "LeafBlock33" }
      (nodeBlock41OutAt s₆ (BitVec.ofNat 8 (G.bs.getD q 0).toNat)) := hl₇
  refine ⟨_, _, hchain₆.append (WalkChain.tail hl₇' (WalkChain.nil hl₇'.inv')), rfl, ?_⟩
  show lookupName (("%Pivot42", .int 1 (evalICmp .slt
      (BitVec.ofNat 8 (G.bs.getD q 0).toNat) (BitVec.ofNat 8 13))) :: s₆.env) "%35" =
    some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
  rw [lookupName_cons_ne _ _ (by decide)]
  rw [hs₆]
  show lookupName (cells
    [("%35", .int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)),
     ("%gep", .ptr ((G.b - 1) + c.toNat))]
    (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)).env)
    "%35" = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
  block_lk

/-- The state `LeafBlock33` leaves at the class that takes the whitespace arm: the
offset's two cells, at `land.rhs.i.preheader`. -/
def leafBlock33OutAt (s : State) (x : BitVec 8) : State :=
  { stateAt (cells
      [("%SwitchLeaf34", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
        (BitVec.ofNat 8 1))),
       ("%.off", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
    pc := "land.rhs.i.preheader", pre := some s.pc }

/-- The state the whitespace scan's preheader leaves: nothing but the edge, at
`land.rhs.i`. -/
def landRhsPreheaderOutAt (s : State) : State :=
  { s with pc := "land.rhs.i", pre := some s.pc }

/-- **The chain extended by `LeafBlock33`'s step.**  A chain to `LeafBlock33` is one step
longer at the class that takes the whitespace arm; the step's two cells are its own, and
its successor is the `def` — no restated nest. -/
theorem walkChain_extend_leafBlock33 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "LeafBlock33")
    {x : BitVec 8} (h35 : lookupName s.env "%35" = some (.int 8 x))
    (hws : evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    WalkChain calls G C₀ s₀ { C with block := "land.rhs.i.preheader" }
      (leafBlock33OutAt s x) := by
  have hres : (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
      then "land.rhs.i.preheader" else "if.end372.i") = "land.rhs.i.preheader" :=
    if_pos hws
  obtain ⟨s', hl, hs⟩ := WalkLink.LeafBlock33_at G C s (WalkChain.inv_last hchain) hblock h35
  have hstep : s' = leafBlock33OutAt s x := by
    rw [hs]
    simp only [leafBlock33OutAt, hres]
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `land.rhs.i.preheader`'s step.**  The block is the edge
alone, so the step is the block's own `br` and its successor is the source state at the
new block and predecessor. -/
theorem walkChain_extend_landRhsPreheader {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i.preheader")
    (hpcs : s.pc = "land.rhs.i.preheader")
    {inner : Nat} (hinner : C.inner = inner)
    (hsc : ScanEntered { s with pc := "land.rhs.i", pre := some s.pc }
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" inner) :
    WalkChain calls G C₀ s₀ { C with block := "land.rhs.i" } (landRhsPreheaderOutAt s) := by
  have hloc : WalkLocal { C with block := "land.rhs.i" }
      { s with pc := "land.rhs.i", pre := some s.pc } := by
    simp only [WalkLocal, hblock]
    rw [hinner]
    exact Or.inr hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.land_rhs_i_preheader_at G C s (WalkChain.inv_last hchain) hblock hloc
  have hstep : s' = landRhsPreheaderOutAt s := by
    rw [hs]
    rfl
  rw [hstep] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- The state `land.rhs.i` leaves: the scan's byte and the address it came from, at
`NodeBlock52`.  The selected `phi`'s cell is the environment the step binds before its
own cells, which is the `bindAll` the helper's conclusion names. -/
def landRhsIOutAt {m0 : Mem} (G : WalkGeom m0) (s : State) (e : BitVec 64) (b : UInt8) :
    State :=
  { stateAt (cells [("%36", .int 8 (BitVec.ofNat 8 b.toNat)),
      ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      (s.bindAll [("%ee.0.i238", .int 64 e)]).env)
      (s.bindAll [("%ee.0.i238", .int 64 e)]) with
    pc := "NodeBlock52"
    pre := some (s.bindAll [("%ee.0.i238", .int 64 e)]).pc }

/-- The state `NodeBlock52` leaves at the class that takes `%36 < 13`: the pivot's cell,
at `LeafBlock43`. -/
def nodeBlock52OutAt (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot53" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))) with
    pc := "LeafBlock43", pre := some s.pc }

/-- The state `LeafBlock43` leaves on the arm that returns to the scan's latch: the
offset's two cells, at `while.body370.i`. -/
def leafBlock43OutAt (s : State) (x : BitVec 8) : State :=
  { stateAt (cells
      [("%SwitchLeaf45", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
        (BitVec.ofNat 8 1))),
       ("%.off44", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
    pc := "while.body370.i", pre := some s.pc }

/-- **The chain extended by `land.rhs.i`'s step.**  The scan's counter `phi`, the
address it indexes and the byte it loads: the byte is the document's own
(`walkDoc_byte`), so the step's price is a byte of the document and nothing else. -/
theorem walkChain_extend_landRhsI {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap) :
    WalkChain calls G C₀ s₀ { C with block := "NodeBlock52" }
      (landRhsIOutAt G s e (G.bs.getD (e.signExtend 64).toNat 0)) := by
  have hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1
      = some [G.bs.getD (e.signExtend 64).toNat 0] :=
    walkDoc_byte G C s (WalkChain.inv_last hchain) halen hevlen hqn
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.land_rhs_i_at G C s (WalkChain.inv_last hchain) hblock hpre hin hv hpos hread
  have hstep : s' = landRhsIOutAt G s e (G.bs.getD (e.signExtend 64).toNat 0) := by
    rw [hs]
    rfl
  rw [hstep] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `NodeBlock52`'s step.**  The scan's byte against `13`, its
arm resolved by the class's bit. -/
theorem walkChain_extend_nodeBlock52 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock52")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hlt : evalICmp .slt x (BitVec.ofNat 8 13) = 1) :
    WalkChain calls G C₀ s₀ { C with block := "LeafBlock43" } (nodeBlock52OutAt s x) := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .slt x (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "LeafBlock43" := if_pos hlt
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.NodeBlock52_at G C s (WalkChain.inv_last hchain) hblock h1
  have hstep : s' = nodeBlock52OutAt s x := by
    rw [hs]
    simp only [nodeBlock52OutAt, hres]
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `LeafBlock43`'s step** — the whitespace skip's leaf taking
the back edge, so the chain arrives at the scan's latch. -/
theorem walkChain_extend_leafBlock43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "LeafBlock43")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hge : evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0)
    {inner : Nat} (hinner : C.inner = inner)
    (hsc : ScanCount (leafBlock43OutAt s x) "%ee.0.i238" "%cond350.i" inner) :
    WalkChain calls G C₀ s₀ { C with block := "while.body370.i" } (leafBlock43OutAt s x) := by
  have hloc : WalkLocal { C with block := "while.body370.i" } (leafBlock43OutAt s x) := by
    simp only [WalkLocal, leafBlock43OutAt, hblock]
    rw [hinner]
    exact hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.LeafBlock43_at G C s (WalkChain.inv_last hchain) hblock h36 hloc
  have hres : (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
      then "if.end372.i" else "while.body370.i") = "while.body370.i" :=
    if_neg (by rw [hge]; decide)
  have hstep : s' = leafBlock43OutAt s x := by
    rw [hs]
    simp only [leafBlock43OutAt, hres]
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- The state the token's dispatch leaves at `NodeBlock41`: the byte's cell and the
address it was read from, on the environment `cond.end349.i`'s run leaves. -/
def headS₆ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (q : Nat) : State :=
  { stateAt (cells
      [("%35", .int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)),
       ("%gep", .ptr ((G.b - 1) + c.toNat))]
      (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)).env)
      (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)) with
    pc := "NodeBlock41"
    pre := some (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok
      (C.stage.tok + 20)).pc }

/-- The state `NodeBlock41` leaves at the class that takes the byte's first arm. -/
def headS₇ {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (q : Nat) : State :=
  nodeBlock41OutAt (headS₆ G C s x inc nep c ix q)
    (BitVec.ofNat 8 (G.bs.getD q 0).toNat)

/-! ### The scan's chain to its latch, as one theorem

The five links from `LeafBlock33` to the latch, composed.  The states are the `def`s
of the links applied in order, so the theorem names the path instead of its nest, and
every premise is a fact about the program at one of those `def`s: the preheader's entry
fact, the byte the scan loads (the document's own), the two pivot bits, and the
counter's bound at the latch. -/
abbrev scanB {m0 : Mem} (G : WalkGeom m0) (e : BitVec 64) : UInt8 :=
  G.bs.getD (e.signExtend 64).toNat 0

/-- The chain's state after `LeafBlock33`. -/
def scanT₁ (s : State) (x : BitVec 8) : State := leafBlock33OutAt s x

/-- The chain's state after `land.rhs.i.preheader`. -/
def scanT₂ (s : State) (x : BitVec 8) : State := landRhsPreheaderOutAt (scanT₁ s x)

/-- The chain's state after `land.rhs.i`: the scan's byte is the document's at the
counter. -/
def scanT₃ {m0 : Mem} (G : WalkGeom m0) (s : State) (x : BitVec 8) (e : BitVec 64) :
    State :=
  landRhsIOutAt G (scanT₂ s x) e (scanB G e)

/-- The chain's state after `NodeBlock52`. -/
def scanT₄ {m0 : Mem} (G : WalkGeom m0) (s : State) (x : BitVec 8) (e : BitVec 64) :
    State :=
  nodeBlock52OutAt (scanT₃ G s x e) (BitVec.ofNat 8 (scanB G e).toNat)

/-- The chain's state at the latch, after `LeafBlock43` takes the back edge. -/
def scanT₅ {m0 : Mem} (G : WalkGeom m0) (s : State) (x : BitVec 8) (e : BitVec 64) :
    State :=
  leafBlock43OutAt (scanT₄ G s x e) (BitVec.ofNat 8 (scanB G e).toNat)

/-- **The scan's chain to its latch.**  `LeafBlock33`'s step under the whitespace arm,
the preheader's edge, the scan's own step (whose byte is `walkDoc_byte`'s), the pivot
on the byte, and the whitespace skip's leaf taking the back edge — one chain, at the
`def`s, ending at `while.body370.i`. -/
theorem walkScanChain_to_latch {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "LeafBlock33")
    {x : BitVec 8} (h35 : lookupName s.env "%35" = some (.int 8 x))
    (hws : evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    -- the preheader's entry fact: the scan's counter and its bound
    (hsc : ScanEntered (scanT₂ s x) "land.rhs.i.preheader" "%idxprom.i" "%cond350.i"
      C.inner)
    -- the byte the scan loads, and the document it comes from
    {e : BitVec 64}
    (hin : phiIncoming "land.rhs.i.preheader"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] =
      some (.reg "%idxprom.i"))
    (hv : evalOperand (landRhsPreheaderOutAt (scanT₁ s x)) (.reg "%idxprom.i")
      = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    -- the byte's two pivots
    (h36₃ : lookupName (scanT₃ G s x e).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)))
    (hlt : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (h36₄ : lookupName (scanT₄ G s x e).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)))
    (hge : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0)
    -- the latch's own counter fact
    (hcount : ScanCount (scanT₅ G s x e) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀ { C with block := "while.body370.i" } (scanT₅ G s x e) := by
  -- `LeafBlock33`
  have h₁ : WalkChain calls G C₀ s₀ { C with block := "land.rhs.i.preheader" }
      (scanT₁ s x) :=
    walkChain_extend_leafBlock33 (C₀ := C₀) (s₀ := s₀) hchain hblock h35 hws
  -- the preheader's edge
  have hpcs : (scanT₁ s x).pc = "land.rhs.i.preheader" := rfl
  have h₂ : WalkChain calls G C₀ s₀
      { { C with block := "land.rhs.i.preheader" } with block := "land.rhs.i" }
      (scanT₂ s x) :=
    walkChain_extend_landRhsPreheader (C₀ := C₀) (s₀ := s₀)
      (C := { C with block := "land.rhs.i.preheader" }) (inner := C.inner) h₁ rfl hpcs rfl hsc
  -- the scan's own step
  have h₃ : WalkChain calls G C₀ s₀
      { { { C with block := "land.rhs.i.preheader" } with block := "land.rhs.i" } with
        block := "NodeBlock52" } (scanT₃ G s x e) :=
    walkChain_extend_landRhsI (C₀ := C₀) (s₀ := s₀)
      (C := { { C with block := "land.rhs.i.preheader" } with block := "land.rhs.i" })
      h₂ rfl rfl hin hv hpos hqn halen hevlen
  -- the pivot on the byte
  have h₄ : WalkChain calls G C₀ s₀
      { { { { C with block := "land.rhs.i.preheader" } with block := "land.rhs.i" } with
        block := "NodeBlock52" } with block := "LeafBlock43" } (scanT₄ G s x e) :=
    walkChain_extend_nodeBlock52 (C₀ := C₀) (s₀ := s₀)
      (C := { { { C with block := "land.rhs.i.preheader" } with block := "land.rhs.i" } with
        block := "NodeBlock52" }) h₃ rfl h36₃ hlt
  -- the whitespace skip's leaf, back to the latch
  exact walkChain_extend_leafBlock43 (C₀ := C₀) (s₀ := s₀)
    (C := { { { { C with block := "land.rhs.i.preheader" } with block := "land.rhs.i" } with
      block := "NodeBlock52" } with block := "LeafBlock43" }) (inner := C.inner) h₄ rfl h36₄
      hge rfl hcount

/-- **The dispatch's chain from the loop head to the scan's latch.**  The twelve links
of the head path and the scan's, as one chain: the two halves are `walkHeadChain`'s and
`walkScanChain_to_latch`'s, and the only thing joining them is that the head's last
state is the scan's first — which is why the `def`s name it.

Every premise is a fact about the program at one of the `def`s: the class's three pivot
bits, the token's arm, the scan's whitespace and its two pivots, the preheader's entry
fact, the byte (`walkDoc_byte`'s), and the counter's own bound.  What remains outside it
is the induction's step — the scan's visit repeated — which `WalkScanInduction` names. -/
theorem walkHeadChain_to_scanLatch {m0 : Mem} {G : WalkGeom m0}
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
    (hevlen : C.evlen ≤ G.evcap)
    (hbit : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD q 0).toNat)
      (BitVec.ofNat 8 13) = 1)
    -- the scan's own premises, at the state the head path reaches
    (hws : evalICmp .ule (BitVec.ofNat 8 (G.bs.getD q 0).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1)
    (hsc : ScanEntered
      (scanT₂ (headS₇ G C s x inc nep c ix q) (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner)
    {e : BitVec 64}
    (hin : phiIncoming "land.rhs.i.preheader"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] =
      some (.reg "%idxprom.i"))
    (hv : evalOperand
      (landRhsPreheaderOutAt
        (scanT₁ (headS₇ G C s x inc nep c ix q) (BitVec.ofNat 8 (G.bs.getD q 0).toNat)))
      (.reg "%idxprom.i") = some (.int 64 e))
    (hpos' : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn' : (e.signExtend 64).toNat < G.n)
    (h36₃ : lookupName (scanT₃ G (headS₇ G C s x inc nep c ix q)
      (BitVec.ofNat 8 (G.bs.getD q 0).toNat) e).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)))
    (hlt : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (h36₄ : lookupName (scanT₄ G (headS₇ G C s x inc nep c ix q)
      (BitVec.ofNat 8 (G.bs.getD q 0).toNat) e).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)))
    (hge' : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0)
    (hcount : ScanCount (scanT₅ G (headS₇ G C s x inc nep c ix q)
      (BitVec.ofNat 8 (G.bs.getD q 0).toNat) e) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain (stage2Calls stage2SubCalls) G C s { C with block := "while.body370.i" }
      (scanT₅ G (headS₇ G C s x inc nep c ix q) (BitVec.ofNat 8 (G.bs.getD q 0).toNat) e) := by
  obtain ⟨C₆, s₆, hchain₆, hC₆, hs₆⟩ :=
    walkHeadChain_to_nodeBlock41 hInv hhead h8 hlt91 hlt44 hne34 hinc hnep hge hugt hpre4
      hinc4 hav4 hidx4 htok4 hgap4 hpos hq63 hqn halen hevlen
  rw [hC₆] at hchain₆
  have hs₆' : s₆ = headS₆ G C s x inc nep c ix q := by
    rw [hs₆]
    rfl
  rw [hs₆'] at hchain₆
  -- the byte's cell, at the state the token's arm left
  have h35 : evalOperand (headS₆ G C s x inc nep c ix q) (.reg "%35")
      = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)) := by
    show lookupName (cells
      [("%35", .int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)),
       ("%gep", .ptr ((G.b - 1) + c.toNat))]
      (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)).env)
      "%35" = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
    block_lk
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G _ _ hchain₆.inv_last rfl h35
  have hres : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD q 0).toNat)
      (BitVec.ofNat 8 13) = 1 then "LeafBlock33" else "NodeBlock39") = "LeafBlock33" :=
    if_pos hbit
  have hstep : s₇ = headS₇ G C s x inc nep c ix q := by
    rw [hs₇]
    simp only [headS₇, nodeBlock41OutAt, hres]
  rw [hstep] at hl₇
  rw [hres] at hl₇
  have hchain₇ := hchain₆.append (WalkChain.tail hl₇ (WalkChain.nil hl₇.inv'))
  -- the byte's lookup at the state `NodeBlock41` leaves
  have h35' : lookupName (headS₇ G C s x inc nep c ix q).env "%35"
      = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)) := by
    show lookupName (("%Pivot42", .int 1 (evalICmp .slt
      (BitVec.ofNat 8 (G.bs.getD q 0).toNat) (BitVec.ofNat 8 13))) ::
      (headS₆ G C s x inc nep c ix q).env) "%35"
      = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
    rw [lookupName_cons_ne _ _ (by decide)]
    show lookupName (cells
      [("%35", .int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat)),
       ("%gep", .ptr ((G.b - 1) + c.toNat))]
      (condEnd349OutAt (headS₄ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)).env)
      "%35" = some (.int 8 (BitVec.ofNat 8 (G.bs.getD q 0).toNat))
    block_lk
  exact walkScanChain_to_latch (C₀ := C) (s₀ := s) hchain₇ rfl h35' hws hsc hin hv hpos'
    hqn' halen hevlen h36₃ hlt h36₄ hge' hcount

/-! ### The five inductions, named

A scan's visit is not a finite path: the scan repeats until its counter reaches its
bound, so what it owes the dispatch is an induction, one per scan.  The five are the
census's `walkScanStepSets` sets — the literal comparison's, the whitespace skip's, the
string scan's, the escape scan's and the extra-token scan's — and each has the same four
pieces, stated once here so the five are five instantiations rather than five arguments:

* **the step** — from the latch, short of the bound, one visit reaches the scan's
  landing block at a count inside one byte's allowance (`stage2ByteAllowance`), and the
  visiting carry is the latch's again with its counter re-pinned.  The *chain* of that
  visit is `walkScanChain_to_latch`'s at the scan's names; reading it as a
  `WalkSegment` is `WalkSegment.of_chain`;
* **the exit** — at the bound the latch's equality test is set, so the terminator takes
  the scan's exit arm; `execTerm_condbr_bit` resolves the arm from the test's bit, which
  is what names the exit's successor;
* **the advance** — the latch's increment is its counter plus one, which is the
  induction's measure: the bound less the counter falls by one per visit, so the visit
  count is bounded by the remaining budget.

The four token scans' lattices are the body's own blocks (`scanBlock`/`scanWhitespace_find`
and its three siblings); the literal comparison's is `for.inc.i.i`.  None of the three
pieces is proved here: what this module proves is the *chain* a visit is made of, and the
price the census charges it (`walkScanStepWidth_le_byteAllowance`), so the inductions
are stated at exactly the facts those two leave for them. -/
structure WalkScanInduction (calls : Calls) {m0 : Mem} (G : WalkGeom m0)
    (latch land inc phi cond exit : String) : Prop where
  /-- **The step**: one visit of the latch, short of the bound, reaching the scan's
  landing block inside one byte's allowance with the increment written.

  The hypothesis is `i + 1 < c`, not `i < c`: the latch's test is `%inc = %cond`, so the
  visit is taken exactly while the increment is *short* of the bound, and `i + 1 = c` is
  the exit.  `c < 2 ^ 64` is the bound's own width: the register holds the word, so a
  `c` above it is the same register value as `c % 2 ^ 64`, and the count `c - i` is only
  the register's remaining distance when `c` is the word.  The re-pinned register is the increment, not the counter: the counter's own
  `phi` is the *landing* block's first instruction, so at the landing block's entry the
  counter still holds the visiting value — a field claiming it advanced there would be
  false, and the visit's counter change is the landing block's `phi` (`ScanLanded`). -/
  step : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = latch →
    ∀ i c : Nat, lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
      c < 2 ^ 64 → i + 1 < c →
      ∃ (C' : WalkCarry G) (s' : State) (j : Nat),
        WalkSegment calls G C s C' s' j ∧ C'.block = land ∧ j ≤ stage2ByteAllowance ∧
        lookupName s'.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
        lookupName s'.env cond = some (.int 64 (BitVec.ofNat 64 c))
  /-- **The exit**: the test is set at `i + 1 = c` — the increment reaching the bound —
  and the terminator is the jump to the scan's own exit block. -/
  exitStep : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = latch →
    ∀ i c : Nat, lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
      c < 2 ^ 64 → i + 1 = c →
      ∃ (s' : State), _root_.LeanLLVM.step calls stage2Body s = .jump s' ∧ s'.pc = exit

/-- The literal comparison's scan: its latch, its landing block and its registers. -/
def walkInductionLiteral (calls : Calls) {m0 : Mem} (G : WalkGeom m0) : Prop :=
  WalkScanInduction calls G "for.inc.i.i" "for.body.i.i" "%inc.i.i" "%i.029.i.i"
    "%cond.i.i" "for.end.i.i"

/-- The whitespace skip's scan — the one `walkScanChain_to_latch` follows to the latch. -/
def walkInductionWhitespace (calls : Calls) {m0 : Mem} (G : WalkGeom m0) : Prop :=
  WalkScanInduction calls G "while.body370.i" "land.rhs.i" "%inc371.i" "%ee.0.i238"
    "%cond350.i" "if.end372.i"

/-- The string scan. -/
def walkInductionString (calls : Calls) {m0 : Mem} (G : WalkGeom m0) : Prop :=
  WalkScanInduction calls G "while.body.i104" "land.rhs.i103" "%inc.i105" "%ee.011.i"
    "%cond.i" "cleanup474.i"

/-- The escape scan. -/
def walkInductionEscape (calls : Calls) {m0 : Mem} (G : WalkGeom m0) : Prop :=
  WalkScanInduction calls G "while.body76.i" "land.rhs71.i" "%inc77.i" "%s2.020.i"
    "%cond.i" "while.end78.i"

/-- The extra-token scan. -/
def walkInductionExtraToken (calls : Calls) {m0 : Mem} (G : WalkGeom m0) : Prop :=
  WalkScanInduction calls G "while.body462.i" "land.rhs457.i" "%inc463.i" "%q.0.i246"
    "%cond350.i" "if.end473.i"

-- Each named latch is a block of the pinned body, so an induction named at a block the
-- body does not carry fails at elaboration rather than at use.
#guard (stage2Body.findBlock "for.inc.i.i").isSome
#guard (stage2Body.findBlock "while.body370.i").isSome
#guard (stage2Body.findBlock "while.body.i104").isSome
#guard (stage2Body.findBlock "while.body76.i").isSome
#guard (stage2Body.findBlock "while.body462.i").isSome

-- The exit each induction leaves by, and the block it lands on, are blocks of the body
-- too — the landing blocks are the five `scanLanding` instances' and the exits are the
-- latches' own second arms.
#guard (stage2Body.findBlock "for.end.i.i").isSome
#guard (stage2Body.findBlock "if.end372.i").isSome
#guard (stage2Body.findBlock "cleanup474.i").isSome
#guard (stage2Body.findBlock "while.end78.i").isSome
#guard (stage2Body.findBlock "if.end473.i").isSome
#guard (stage2Body.findBlock "for.body.i.i").isSome
#guard (stage2Body.findBlock "land.rhs.i").isSome
#guard (stage2Body.findBlock "land.rhs.i103").isSome
#guard (stage2Body.findBlock "land.rhs71.i").isSome
#guard (stage2Body.findBlock "land.rhs457.i").isSome

-- And each exit is its latch's `condbr` target, so the induction's `exit` is the arm the
-- latch itself names rather than a block the step has to travel through.
#guard (decide ((scanBlock "for.inc.i.i" "%inc.i.i" "%i.029.i.i" "%exitcond.not.i.i"
  "%cond.i.i" "for.end.i.i" "for.body.i.i").term = Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.i.i" "for.body.i.i"))
#guard (decide ((scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
  "%cond350.i" "if.end372.i" "land.rhs.i").term = Term.condbr (Operand.reg "%exitcond.not") "if.end372.i" "land.rhs.i"))
#guard (decide ((scanBlock "while.body.i104" "%inc.i105" "%ee.011.i" "%exitcond.not.i"
  "%cond.i" "cleanup474.i" "land.rhs.i103").term = Term.condbr (Operand.reg "%exitcond.not.i") "cleanup474.i" "land.rhs.i103"))
#guard (decide ((scanBlock "while.body76.i" "%inc77.i" "%s2.020.i" "%exitcond24.not.i"
  "%cond.i" "while.end78.i" "land.rhs71.i").term = Term.condbr (Operand.reg "%exitcond24.not.i") "while.end78.i" "land.rhs71.i"))
#guard (decide ((scanBlock "while.body462.i" "%inc463.i" "%q.0.i246" "%exitcond298.not"
  "%cond350.i" "if.end473.i" "land.rhs457.i").term = Term.condbr (Operand.reg "%exitcond298.not") "if.end473.i" "land.rhs457.i"))

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_lt91
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_lt91_lt44
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_default
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_to_condOut
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_to_nodeBlock41
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_to_nodeBlock41Out
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_leafBlock33
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_landRhsPreheader
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_landRhsI
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_nodeBlock52
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_leafBlock43
#print axioms LeanLLVM.Refinement.WalkScope.walkScanChain_to_latch
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_to_scanLatch

end WalkScope

end LeanLLVM.Refinement
