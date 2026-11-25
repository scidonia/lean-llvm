/-
The no-event walk's parent-closer arm: the container rows' second missing route.

`JsonStage2NoEventWalkRowsReady`'s container producers place the closer arm on
the **comma continuation**.  An empty pair whose closer is the last element of its
parent is not that shape: the entry after the pair's closer (`k + 2`) holds the
*parent's* closer, so the separator the shared cycle reads there is `]` (`93`) or
`}` (`125`), not the comma (`44`).  `Stage2NoEventWalkPairBranch.comma` is then
false, `stage2NoEventWalkBracketRow_of_head`/`…BraceRow_of_head` have no
inhabitant of their `hg` premise, and the depth-zero routes do not apply either —
they take `sp = 0`, and a nested pair's depth is positive.

This module states that route and reduces it, without inventing the producer the
tree lacks:

* **the committed producer's premise is empty here** (proved here).  A head whose
  `k + 2` byte is `]`/`}` refutes `Stage2NoEventWalkPairBranch` outright, so the
  closer arm's in-tree producer cannot be instantiated, and the gap is not a
  missing hypothesis but a false one;
* **the route, for the `]` class** (proved here, at premises named below).  The
  pair's own route takes the head to `after_value`'s entry at index `k + 2`, at
  the bracket pair's carry (`tok + 2`, `terms + 7`).  The parent's dispatch then
  reads the *same* entry (`if.end378` loads `%k.6 = k + 2`'s lane and its
  document byte) and takes its own closer arm: `if.end410` → `NodeBlock41` (the
  byte is not `,`) → `LeafBlock39` → `do.body417` → `close_arr` →
  `after_value` at index `k + 3`, one event and four terms heavier and one depth
  lower.  From there the walk is at **the same `after_value` interface at the
  parent's index**: a non-zero frame, the depth one lower than the pair
  endpoint's, and — where the parent's container continues — the next entry's
  comma continuing to the next element's head.  The route is therefore the pair's
  route, the parent's closer arm, and the committed cycle
  (`stage2NoEventWalkCycle_of_afterValue`) at `k + 3` instead of `k + 2` — the
  same closer arm at the parent's index.

**The premises, and where each comes from.**

* `hjl : jl ≤ 64` and the pair route's price `jl + Φ Kc (k+2) ≤ Φ K k` — **proved
  here** (`stage2NoEventWalkPairRoutePrice`): the pair route advances two entries,
  so any count up to two entries' allowance (`64`) is payable; the `[]` leg's
  eleven blocks fit.
* `hleg` — the pair's route from the head to `after_value(k+2)` at the pair's
  carry — **not in this tree at this shape**.  The committed leg
  (`stage2NoEventWalkBracketPairLeg`, eleven blocks, `…RowsContainerB`) *states*
  the route only together with `hcomma`, and this module's refutation shows that
  premise is false under `…ParentSep`; so the leg's statement is not
  instantiable here, and only its segment — the eleven blocks without the
  endpoint bundle, which does not consume `hcomma` — is the route.  The segment
  has to be re-proved without the bundle; what the bundle would carry is this
  shape's separator (`…ParentSep` at `93`), not a comma.
* `hparent` — the parent's closer arm, `after_value(k+2)` → `after_value(k+3)` —
  **not in this tree**.  The `]` arm's `LeafBlock39` and `do.body417` have no
  denotation here (the `,` sibling is the committed cycle's `LeafBlock37`).
* `hpprice` — the parent arm's allowance, `p + Φ Kp (k+3) ≤ Φ Kc (k+2)` — **the
  caller's post**.  The arm advances one entry and its own blocks' price is the
  caller's to discharge; this module does not bound it (the tree's only `∃ p`
  cycle, `stage2NoEventWalkCycle_of_pair`, carries no allowance either).
* `hsrc` — `Stage2NoEventWalkCycleSrc` at `k + 3`: the closer interface one level
  up (non-zero frame and depth, the `after_value` entry, the next entry's comma) —
  **the caller's post**, and the point of the reduction: the shape is not a new
  endpoint, it is the *same* closer arm shifted to the parent's index.  Its
  `klt` gives the target's liveness; the committed cycle gives the head at
  `k + 4` at the same carry.

**A26 addendum — the `}` class is not delivered here.**  The review's two
objections hold, and the brace instance is therefore absent:

* the brace pair leg lands at the carry `tok + 2`, `terms + 3`
  (`…RowsBrace.lean:772`), not the bracket's `terms + 7`; a `terms + 7` premise
  has no brace producer, and reusing it would misprice the leg by four terms;
* the `}` closer arm (`if.then384` → `NodeBlock35` → `LeafBlock33` →
  `do.body391`) is reachable only at `frame = 0`, while **both** pair legs' endpoint
  bundles take the frame word from the popped stack byte, `bytesToNat bs = fr` with
  `1 ≤ fr` (`…RowsContainerB.lean:735`, `…RowsBrace.lean:1017`) — so the two
  premises cannot hold at one state.  The `{"a": {}}` shape has `frame = 0` at
  the *pair's head*, which both legs exclude through the same `1 ≤ fr`, so it has
  no in-tree pair route either.

So the parent-closer shape is proved for the `]` class; the `}` class needs one
artifact the tree does not have — a brace pair route that ends at `frame = 0`
with `sp ≥ 1` (the committed brace pair leg demands `1 ≤ fr` at its endpoint and
`…BraceZeroRoute` demands `sp = 0`).  `do.body391` itself is denoted, but only at
a frame-zero endpoint keyed to `…CycleFrameZero`'s own source, not to the pair's;
so the missing piece is the pair route, and the arm's denotation is the second
thing such a route would have to meet.  That is a finding about the tree's
coverage, not about this proof.  `stage2NoEventWalkCloserCarry`'s `dc`
still names both arms' term deltas (`4` for `do.body417`'s `%add419`, `2` for
`do.body391`'s `%add393`), because the composition lemma is agnostic about which
closer produced the segment; only the `dc = 4` instance is instantiable.

What is **not** proved here, and is not claimed: the parent's arm itself (a
segment with its blocks' denotations), the pair's segment (see `hleg`), and any
row at the shifted endpoint that does not come from the committed cycle — at
depth one the shifted endpoint's `after_value` takes the terminal lane
(`if.then357`), whose evidence is the caller's post exactly as `…ZeroRow`'s is.
The reduction says the gap is the `after_value` dispatch's closer arm, not a
head-level route.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsReady
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps
  (readBytes_writeBytes_frame readBytes_length)

/-! ### The shape's separator

The pair's row reads the entry after the pair's closer and asks it to be a comma.
In this shape it is the parent's closer, so the entry's document byte is the
class's own bracket (`93`/`125`).  The predicate names that byte at the shape's
index, `k + 2`. -/

/-- **The entry at `k + 2` holds the parent's closer**: its document byte is `x`
(`93` for a `[]` element, `125` for a `{}` one). -/
def Stage2NoEventWalkParentSep (K : Stage2NoEventWalkCarry) (k : Nat) (x : Nat) : Prop :=
  ∀ q, K.ent[k + 2]? = some q → (K.bs.getD q 0).toNat = x

/-- **An entry exists at an index below the entry count.**  The entry stream's
length is the count (`Inv.entries`), so an in-range index has a lane. -/
theorem Stage2NoEventWalkHead.entGetElem? {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) {j : Nat}
    (hj : j < K.nep) : ∃ q, K.ent[j]? = some q := by
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hi : j < K.ent.length := by omega
  exact ⟨K.ent[j], List.getElem?_eq_getElem hi⟩

/-- **The committed closer arm's branch predicate is empty at the parent's
closer.**  `PairBranch.comma` asks the entry at `k + 2` for a comma; the shape's
separator gives it the bracket, and the two bytes differ. -/
theorem stage2NoEventWalkPairBranch_absurd_of_parentSep
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {x q : Nat}
    (hsep : Stage2NoEventWalkParentSep K k x) (hx : x ≠ 44)
    (hq : K.ent[k + 2]? = some q) :
    ¬ Stage2NoEventWalkPairBranch K k s := by
  intro hg
  have h44 : (K.bs.getD q 0).toNat = 44 := by
    rw [hg.comma q hq]
    decide
  have hx' := hsep q hq
  omega

/-- **The empty array's closer arm has no branch at the parent's `]`.**  This is
the `[]` shape: the entry at `k + 2` is the enclosing array's closer. -/
theorem stage2NoEventWalkBracketPairBranch_absurd
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {q : Nat}
    (hsep : Stage2NoEventWalkParentSep K k 93) (hq : K.ent[k + 2]? = some q) :
    ¬ Stage2NoEventWalkPairBranch K k s :=
  stage2NoEventWalkPairBranch_absurd_of_parentSep hsep (by decide) hq

/-- **The empty object's closer arm has no branch at the parent's `}`.** -/
theorem stage2NoEventWalkBracePairBranch_absurd
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {q : Nat}
    (hsep : Stage2NoEventWalkParentSep K k 125) (hq : K.ent[k + 2]? = some q) :
    ¬ Stage2NoEventWalkPairBranch K k s :=
  stage2NoEventWalkPairBranch_absurd_of_parentSep hsep (by decide) hq

/-- **The shape at a live head.**  At a head with room for the pair's own
liveness (`k + 3 < K.nep`), the entry at `k + 2` exists, so the parent's closer
refutes the committed branch predicate without a further existence premise. -/
theorem stage2NoEventWalkBracketPairBranch_absurd_of_live
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) (hlive : k + 3 < K.nep)
    (hsep : Stage2NoEventWalkParentSep K k 93) :
    ¬ Stage2NoEventWalkPairBranch K k s := by
  obtain ⟨q, hq⟩ := h.entGetElem? (j := k + 2) (by omega)
  exact stage2NoEventWalkBracketPairBranch_absurd hsep hq

/-! ### The carries the route moves

The `[]` pair's route adds its two events and seven terms (`…RowsContainerB`); a
closer adds one event and its arm's terms (`4` from `do.body417`'s `%add419` for
the `]` arm, `2` from `do.body391`'s `%add393` for the `}` arm).  The potential
reads none of these fields, so the pair route's price is the same at either
carry. -/

/-- **The bracket pair's carry**: the `[]` pair's two events and seven terms
(`…RowsContainerB`'s leg).  The brace leg's is `terms + 3` and is not this
def's — see the header's A26 addendum. -/
def stage2NoEventWalkPairCarry (K : Stage2NoEventWalkCarry) : Stage2NoEventWalkCarry :=
  { K with tok := K.tok + 2, terms := K.terms + 7 }

/-- **A closer's carry**: one closer event and `dc` terms.  Only `dc = 4` (the
`]` arm) is instantiable from a pair endpoint here; `dc = 2` names the `}` arm's
delta for the composition lemma, which is agnostic about the arm. -/
def stage2NoEventWalkCloserCarry (K : Stage2NoEventWalkCarry) (dc : Nat) :
    Stage2NoEventWalkCarry :=
  { K with tok := K.tok + 1, terms := K.terms + dc }

/-- **The pair's carry leaves the potential alone.** -/
theorem stage2NoEventWalkPairCarry_potential (K : Stage2NoEventWalkCarry) (k : Nat) :
    stage2NoEventWalkPotential (stage2NoEventWalkPairCarry K) k =
      stage2NoEventWalkPotential K k := rfl

/-! ### The pair route's price, proved here

The pair route advances two entries, so its count is payable from two entries'
allowance whatever the route's own block count (eleven for the `[]` leg) — the
arithmetic is `stage2NoEventWalkPotential_add`'s at `d = 2`. -/

/-- **The pair route's price at any count up to two entries' allowance.**  The
endpoint's index must be inside the entry stream (`k + 2 < K.nep`): the entries'
order is what makes the potential fall, and `getD` past the end would default to
zero. -/
theorem stage2NoEventWalkPairRoutePrice {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s)
    {jl : Nat} (hjl : jl ≤ 64) (hk2 : k + 2 < K.nep) :
    jl + stage2NoEventWalkPotential (stage2NoEventWalkPairCarry K) (k + 2) ≤
      stage2NoEventWalkPotential K k := by
  have hpot := stage2NoEventWalkPairCarry_potential K (k + 2)
  rw [hpot]
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 2) 0 :=
    stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 2)
    (Nat.le_of_lt hk2) hentle
  have h32 : 32 * 2 = 64 := by decide
  rw [h32] at hadd
  omega

/-! ### The reduction

The pair's route, the parent's closer arm and the committed cycle at the shifted
index compose to a continuing row: one head segment from the closer head to the
head at `k + 4`, priced by the three legs' own credits. -/

/-- **The closer head's row, from the pair route and the parent's closer arm.**

The pair's route reaches `after_value(k + 2)` at the `[]` pair's carry; the
parent's `]` arm reaches `after_value(k + 3)` one event and `dc` terms heavier;
the committed cycle at `k + 3` returns to the head at `k + 4` at the same carry.
The row advances four entries, `2 + 1 + 1`.

Premises: `h` is the head (as every producer takes it); `hleg` is the pair's
route (**not in this tree at this shape** — the committed leg's *statement* also
demands `hcomma`, false under `…ParentSep`, so only its segment is the route and
that has to be re-proved without the endpoint bundle); `hparent` is the parent's
`]` closer arm (**not in this tree**); `hpprice` is that arm's allowance (**the
caller's post**); `hsrc` is `after_value`'s entry one level up with the comma that
continues the walk (**the caller's post**).  The pair route's price,
`jl + Φ Kc (k+2) ≤ Φ K k`, is **proved here** from `hjl`, `h` and the room past
the endpoint that `hsrc.klt` gives.  Only `dc = 4` is instantiable here; the `}`
class has no pair route at its endpoint (header's A26 addendum). -/
noncomputable def stage2NoEventWalkRow_of_parentCloser
    {calls : Calls} {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat}
    {s sE sE' : State} {jl p dc : Nat}
    (h : Stage2NoEventWalkHead K mem k s)
    (hjl : jl ≤ 64)
    (hleg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkPairCarry K) sE jl)
    (hparent : Stage2NoEventWalkSegment calls mem (stage2NoEventWalkPairCarry K) sE
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) dc) sE' p)
    (hpprice : p + stage2NoEventWalkPotential
        (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) dc) (k + 3) ≤
      stage2NoEventWalkPotential (stage2NoEventWalkPairCarry K) (k + 2))
    (hsrc : Stage2NoEventWalkCycleSrc calls mem
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) dc) (k + 3) sE') :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let w := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' : State := Classical.choose w
  have hwspec := Classical.choose_spec w
  let q : Nat := Classical.choose hwspec
  have hcyc : Stage2NoEventWalkCycle calls mem
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) dc) (k + 3) sE' 1 s' q :=
    Classical.choose_spec hwspec
  have hk2 : k + 2 < K.nep := by
    have h := hsrc.klt
    simp only [stage2NoEventWalkCloserCarry, stage2NoEventWalkPairCarry] at h
    omega
  have hcredit : jl + p + q + stage2NoEventWalkPotential
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) dc) (k + 4) ≤
      stage2NoEventWalkPotential K k := by
    have hleg' := stage2NoEventWalkPairRoutePrice h hjl hk2
    have hcyc' := hcyc.headPriced.credit
    rw [show k + 3 + 1 = k + 4 from by omega] at hcyc'
    omega
  refine Stage2NoEventWalkRow.cont (F := F)
    (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) dc) (k + 4) s'
    (jl + p + q) ?_ rfl rfl rfl (by omega) ?_
  · refine ⟨?_, hcredit⟩
    exact ⟨(hleg.trans hparent).trans hcyc.headPriced.seg.seg,
      hcyc.headPriced.seg.head', hcyc.headPriced.seg.trace'⟩
  · have h := hsrc.klt
    simp only [stage2NoEventWalkCloserCarry, stage2NoEventWalkPairCarry] at h
    omega

/-! ### The `]` class's instance

The bracket pair's `]` closer adds four terms (`do.body417`'s `%add419`) and its
pair route is the leg's eleven blocks.  This is
`stage2NoEventWalkRow_of_parentCloser` at `dc = 4`, `jl = 11`; the `}` class's
instance is absent — it has no pair route at `frame = 0` (header's A26
addendum). -/

/-- **The empty array's row at the parent's `]`.**  `dc = 4` (`do.body417`'s
`%add419`), `jl = 11` (`stage2NoEventWalkBracketPairLeg`'s eleven blocks). -/
noncomputable def stage2NoEventWalkBracketParentCloserRow
    {calls : Calls} {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat}
    {s sE sE' : State} {p : Nat}
    (h : Stage2NoEventWalkHead K mem k s)
    (hleg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkPairCarry K) sE 11)
    (hparent : Stage2NoEventWalkSegment calls mem (stage2NoEventWalkPairCarry K) sE
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4) sE' p)
    (hpprice : p + stage2NoEventWalkPotential
        (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4) (k + 3) ≤
      stage2NoEventWalkPotential (stage2NoEventWalkPairCarry K) (k + 2))
    (hsrc : Stage2NoEventWalkCycleSrc calls mem
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4) (k + 3) sE') :
    Stage2NoEventWalkRow calls mem F K k s :=
  stage2NoEventWalkRow_of_parentCloser h (by decide) hleg hparent hpprice hsrc

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkHead.entGetElem?
#print axioms stage2NoEventWalkPairBranch_absurd_of_parentSep
#print axioms stage2NoEventWalkBracketPairBranch_absurd
#print axioms stage2NoEventWalkBracePairBranch_absurd
#print axioms stage2NoEventWalkBracketPairBranch_absurd_of_live
#print axioms stage2NoEventWalkPairCarry_potential
#print axioms stage2NoEventWalkPairRoutePrice
#print axioms stage2NoEventWalkRow_of_parentCloser
#print axioms stage2NoEventWalkBracketParentCloserRow

end LeanLLVM.Refinement
