/-
# The continuing entry's path to the merge, priced

## The vacuity this module's bundle used to have

The prefix this file composed was `hlastPrefixSeg`'s, and that lemma is the **last**
entry's: it takes `sw.default.i`'s count test on its *failing* arm, so the walk leaves for
`cond.end349.i` directly.  A continuing entry passes the test, and its path leaves through
`cond.true345.i`, which reads the *next* entry's position lane.  The bundle nevertheless
carried the test's value as

  `hge : evalICmp .ult inc nep = 0`

and the arithmetic that makes that contradiction visible is three substitutions.  At a
head state `%inc.i = C.k + 1` (the header binds `%inc.i` as `%k.0.i249 + 1`) and
`%nep = G.nep` (`%nep` is a call argument, and no block of the walk rebinds it), so
`evalICmp .ult inc nep = 0` **is** `¬ (C.k + 1 < G.nep)` — the last entry's equation —
while this module's consumer carries `hk : C.k + 1 < G.nep`.  The two cannot both hold, so
no state inhabited the bundle: `walkRevolution_seg` was true for the wrong reason and
`WalkDispatch`'s continuing case was never produced.  The contradiction was invisible
because the bundle is stated before its consumer exists and each field is true of *its own*
path — the failing arm's value is a true fact about the last entry — so nothing inside the
bundle's module reads one group against another.  The repair is three things, and this file
is all three: the test's field is named `hnext` and carries `= 1`; the prefix is
`hcontPrefixSeg` (`JsonStage2WalkRevolutionPrefix`), the counted path through
`cond.true345.i`; and the groups read from the path are re-stated at that prefix's states.

**A field name that says "greater or equal" for a test whose value is *false* is what hid
this.**  `hnext` names the proposition it carries: a continuing entry has a next one, so
the test succeeds.

## The composition

| piece | lemma | span | count |
|---|---|---|---|
| head: four pivots, `sw.default.i`, `cond.true345.i`, `cond.end349.i` | `hcontPrefixSeg` | head → `cond.end349.i` | `7` |
| the whitespace check: `land.lhs.true357.i`, `NodeBlock41`, `NodeBlock39`, `LeafBlock35` | `hcontPrefixSeg` | → the token's end | `4` |
| seam | `WalkLink.if_end372_i_at` | `if.end372.i` → the class-C span | `1` |
| visits of the extra-token scan | `contScanRounds` | the latch → its last visit | `≤ 8·(v - 1 - ei)` |
| exit | `scanExitSeg` | the latch → `if.end473.i` | `1` |
| merge | `walkIfEnd473_at` | `if.end473.i` → `cleanup478.i` | `1` |

`23 + 1 + 1` is the prefix plus the exit and the merge, and the visits are a counted
traversal rather than part of the prefix.  The visits are composed at
`walkScanRounds457_of_cell`'s **round**, not at that lemma: its conclusion keeps only the counter
at the target (`%q.0.i246 = c - 1`), and the exit test reads the bound (`%cond350.i = c`)
as well, so the traversal's own aggregation cannot reach the exit.  `contScanRounds` is
that aggregation with both registers kept; its measure, its price and its induction are
`walkScanRounds457_of_cell`'s.  Its induction consumes one row, the visited byte's class at the
indices the scan walks (`hbyte`); the round is a theorem of the visit's own premises
(`scanRoundField`, `JsonStage2WalkRevolutionScanRound`) and no guard hypothesis enters.
`ScanGuard`'s `∀` quantifies over every natural pair carrying the two register words, and
above the word's width the subtraction saturates, so the statement is false at any state
whose registers hold words: it was never a fact about the walk, and the round's proof
never read it.

## The price

`23 + n + 2` steps, at `n ≤ 8·(v - 1 - ei)`, against `32·1 + 8·ΔA` and `k2 = C.k + 1`:
the visit count is the entry's span, `v - 1 - ei ≤ entryPos (C.k + 1) - entryPos C.k`, so
`27 + n ≤ 27 + 8·ΔA ≤ 32 + 8·ΔA`.  The fixed part grew from the last entry's `22` to `27`
— the eight extra links are the count test's succeeding arm and the whitespace check — and
it still fits the entry allowance, so the bound is not widened.  Two premises state the
span, because the scan's bound and its first index are the *document's* numbers and neither
is invariant-carried:

* `hspan : v ≤ entryPos G (C.k + 1)` — the scan stops at or before the next entry;
* `hstart : entryPos G C.k ≤ ei` — it starts at or after this one.

From those two `v < 2 ^ 64` and `v ≤ 2 ^ 63` are arithmetic (`entryPos_lt`, `maxDoc`), so
they are not premises.

## The arm this bundle describes, and the arm it cannot

The `hnext`/`hk` contradiction is gone, and there is a second boundary behind it, found the
same way — by a field against the path's own arithmetic.  `if.end372.i`'s `%ee.1.i` `phi`
selects `%cond350.i` on the three leaf edges, and on this path `%cond350.i` is the lane's
word, so the token's end is `v.toNat`; `if.then447.i`'s target then tests
`ult ei %cond350.i` and, with `ei` the scan's index, the cell is the same word:

* `contEntry_ee` — `%ee.1.i` at the scan's entry is `ofNat 64 v.toNat`;
* `contEntry_scan_empty` — therefore **`¬ (ei < v.toNat)`**.

So this bundle's own `heicd` (`ei < v.toNat`) is uninhabited on the arm where the byte
before the entry's end is **not** whitespace.  That is not a defect in the segment — the
walk really does take that path — it is the bundle naming the wrong *continuation*: with an
empty extra-token span the walk leaves the copy call for `if.end473.i` and never enters the
scan, so that arm's segment is shorter and ends at the merge.  The bundle therefore
describes **the whitespace arm**: the byte before the entry's end is `9`, `10`, `13` or
`32`, the whitespace skip runs, the token ends at the first whitespace byte `k < v.toNat`,
and the extra-token scan runs `[k, v.toNat)`.

**The other three classes' arm is a layer boundary, not a missing bundle.**  It is the
cheaper path — seam, class-C span, tail, then `if.end473.i` and the merge, no scan — but it
cannot be taken as a `WalkLink`: `WalkLocal` at `land.rhs457.i` is
`ScanLanded … ∨ ScanEntered …`, and both conjuncts are `∃ i c, c - i ≤ inner ∧ i < c ∧ …`.
On this path `ei` *is* the bound, so the landing sibling's local is uninhabited there and
`WalkLink.if_then447_i`'s `hlt : ei < cd` cannot hold.  A scan-free bundle stated against
that step would be the fourth bundle naming a continuation no state reaches.  The arm needs
a zero-length case in `WalkLocal` at `land.rhs457.i` — `ScanEntered` relaxed to `i ≤ c`, or
a `ScanEmpty` disjunct — which is a vocabulary change of the same kind and size as the
`%inc.i`/`%nep` clause above, and it is a decision about the layer rather than a proof.

## The third of its kind, and the method step it names

Three bundles in this chain named a continuation that no state reaches, and each was found
by the same instrument — reading the field against the path's own arithmetic:

| field | the value it named | the arithmetic that refutes it |
|---|---|---|
| `hge = 0` | the count test's *failing* arm | `%inc.i = C.k + 1`, `%nep = G.nep`, so it is `¬ (C.k + 1 < G.nep)`; the consumer carries `C.k + 1 < G.nep` |
| `hugt = 0` | the byte test's *failing* arm | a continuing entry's `%cond350.i` is the next entry's position, above its own index, so the test is `1` |
| `heicd : ei < v.toNat` | the scan's *non-empty* span | on this arm `%ee.1.i` is `%cond350.i`, so `ei = v.toNat` and the field is `v.toNat < v.toNat` |

That is not three mistakes.  It is one missing step in the method: **trace the path, then
name the fields.**  Each bundle was written by reading a *similar* path's fields and
adjusting the ones the new case was thought to change; the field that was wrong in each case
was one whose value is fixed by an arm three blocks away, and no field's type reads another
field's path.  A bundle author who traces the arm to its end — including the two guards on
it, the count test and the byte test, and the span the scan is entered on — before writing a
field, cannot make this class of error; and a reviewer now has the instrument that finds it:
substitute the arm's own values into every field that names a test, a bound or a span.

## `%cond350.i` is one number, not two

The bound the scan reads is the entry's end, and that is the word `cond.true345.i`
loaded: `%cond350.i` is bound once, at `cond.end349.i`, and no block from there to the
latch rebinds it.  So the bundle carries the lane's word `v` and no separate bound
witness — `contLatch_cond` (`JsonStage2WalkRevolutionPrefix`) is the peel that says the
latch's cell is `ofNat 64 v.toNat`.  A second witness would be one fact written twice.

**`hugt` is arm-specific, and both arms' values are right.**  This bundle's `hugt` is
`ugt (ofNat 64 v.toNat) ix = 1`: the entry is non-empty, `%cond350.i` is above `%idxprom.i`,
so `cond.end349.i` takes `land.lhs.true357.i` and the walk reads the byte before the end.
`HlastFacts.hugt` is `= 0`, and that is the last entry's arm: its `%cond350.i` is `%4`, and
the last entry's position is the stream's end.  Two bundles can share a field name and
correctly carry opposite values; a docstring that gives one value without its arm reads as
a contradiction in the other.

## What is supplied, and what is derived

Three groups are premises because the model's own layer does not produce them:

* the document's bytes and classes — the head's byte and its four pivot bits, the byte
  before the entry's end (`b35`) and its three class bits, the seam's byte and its two
  literal tests, and the second byte's class.  Which byte the document holds is not the
  walk's: `WalkGeom` fixes the addresses and the extents, not the values;
* the visited byte's class (`hbyte`'s two bits at `wsByte G (p + 1)`): the input's
  totality at every index the scan visits, which the model branches on and does not store.
  The row's *read* is not supplied: `scanByteField` produces the address (`%3 = G.b`),
  the document read (`walkDoc_byte`), the loaded register (`landRhs457OutAt`'s `%47` cell)
  and the three local facts, leaving only the class of `G.bs.getD (p + 1) 0`.  The round
  (`scanRoundField`) and the token's register (`scanTokField`) are derived in the same
  module, the latter from `WalkInv.regs`; no guard hypothesis is carried, because
  `ScanGuard` is false at every state whose registers hold words (see above).

Everything else is derived: the `phi`'s selection at `cond.end349.i` is a closed
computation (`contPhi6`), so no witness for it is carried; `%cond350.i`'s value at the
latch is `cond.end349.i`'s own cell; the exit's local fact holds because `if.end473.i` is
not one of `WalkLocal`'s scan blocks; and the inner budget at the last visit is the
invariant's local clause read at the counts the traversal reports (`ScanCount.same`).

## A′: two bundles, a `Sum`, and what is planned rather than landed

The partition is not a set of unrelated producers.  This bundle describes **one of two
continuations** of a continuing entry, and the plan is two structures with a `Sum` at the
`∀`:

* **`HcontFacts` — the whitespace arm, which is what this module's bundle is.**  The byte
  before the entry's end is `9`, `10`, `13` or `32`, the whitespace skip runs, the token
  ends at the first whitespace byte `k`, and the extra-token scan runs `[k, v.toNat)`.
* **`HcontCleanupFacts` — the scan-free arm, landed beside it.**  The token ends at the
  entry's end, so `if.then447.i`'s target tests `ult v v` and leaves for `if.end473.i`: the
  segment goes straight to the merge.  It carries **no** `%ee.1.i` stopper, **no** landing
  group, **no** traversal premises and **no price conjunct with a byte term**
  (`p + 2 ≤ 32·Δk`, `p = 21`).  Its tail is `consumerTailSegEmptyAt`'s three links and its
  closing step is `WalkLink.if_then447_i_empty`.
* `WalkContinueFacts` is a **class, not a `Sum`**: its evidence is `HcontArm`
  (`JsonStage2WalkDispatchHcontArms`), one constructor per class of the emitted head
  switch — the plain-value numeral route (`HcontScalarFacts`), the high-byte route's
  `ws` (`HcontFacts`) and `cleanup` (`HcontCleanupFacts`), the standalone string
  (`HstringFacts`, whose merge index is `C.k + 2`, **at `C.sp = 0` only** — the
  positive-depth opener's `land.lhs.true.i` route has no constructor) beside its
  residue, and the arms for
  the delimiter and token classes (comma, colon, container opener, closer, letters,
  class C, `f` and the run) — and the consumer splits once.  An inductive rather than a
  nested `Sum` because a `Sum` of the arms would re-shape every consumer twice, and the
  class question is still
  asked once, where the class is known.  A conditional inside a `Type`-valued structure
  would make every field a question.

**The run's refinement, landed.**  The whitespace arm's seam is not
class-indexed: the run stops at the first whitespace byte, so its last visit leaves through
`LeafBlock43`, `46` or `48`, whose states differ in the cells each bounded.  So the endpoint
is **data**, and it is no longer the bundle's to carry:

* the class is one field, `hClass`, and the run is derived from it: `contWsRunF` takes the
  class and the whitespace check's own invariant, and returns the segment from
  `contLandS`'s target to the seam as `∃ N, N ≤ 5·(k - i) + 10 ∧ WalkSegment … N` with the
  stop's `%cond350.i` cell beside it — the count existential because the three leaves differ
  in cost.  Its source and its endpoint are the total functions `wsPreS` and `wsSlS`, so the
  bundle's other fields state their states without carrying a state.
* `hopS` is **produced** (`contWsEntry_hopS`: the seam stores `ofNat 64 k`, and the scan's
  phi selects `%ee.1.i` on `if.then447.i`'s edge), so the bundle carries no landing index
  and the contradiction with `heicd` is gone.
* The class is a field rather than the run's business: a `Type` has to be inhabited at every
  head state with an entry left, and the run exists only where `%35` enters the skip.  The
  exit set `{43, 46, 48}` is the complement of the entry leaves `{33, 35, 37}`, and that
  complement check is what caught an arm list's error in a draft.
* The seam's `%end.i` cell is the head state's static register, transported to the endpoint
  by `wsSlS_envEnd` and read off `WalkInv.regs` — so the seam's link needs no supply either.

**The price, and why the byte budget is not double-spent.**  The run is `≤ 5·(k - i)` and
the scan's visits are `cd - 1 - k`, so `5(k-i) + 8(cd-1-k) ≤ 8(cd-1-i) ≤ 8·ΔA`: the prefix
is `28 + 5(k - i)` and the total `30 + 8·ΔA ≤ 32·Δk + 8·ΔA`, two steps spare.  **The budget
is not double-spent precisely because the scan's start *is* the run's stop**; a prefix that
ran the skip and still started the scan at `i` would charge `8·ΔA` twice and the bound would
fail.  (The fuller derivation, with the per-visit link count and the layer's share, is in
`JsonStage2WalkRevolutionPrefix`'s header.)

**And the finding that outlives the plan:** `hge`, `hugt` and `heicd` each named a
continuation no state reaches, and the build was green through all three.  The method step
is **trace the path, then name the fields** — with the checks these three turns added: every
name a field type mentions must be a field; a `Type` field needs a `Prop`-free term; an arm
list is a set with a complement, so state the complement; and a `condbr` link owes the local
at *both* arms, including the one it does not take.

## Two of the merge's cells are invariant clauses

The merge's cells state `%inc.i = ofNat 64 (C.k + 1)` and `%nep = ofNat 64 G.nep` at
`cleanup478.i`, and both now follow from `WalkInv` clauses: `%inc.i` is bound once, in the
header, as `%k.0.i249 + 1`, so `WalkInv.inc_reg` holds wherever `blockIndex` holds, and
`%nep` is a parameter no block rebinds, so it is one of `walkStaticRegs`' pairs and
`WalkInv.regs` reads it.  Adding them was a vocabulary change — a scoping pass measured 39
`WalkInv` construction sites in 10 modules, `whileBody_step` (the only block that rebinds
`%inc.i`) and two new disequalities in `WalkPtrs.bind`/`WalkRegs.bind` — and it retired two
of the merge's three conjuncts and not the third: `Cd.k = C.k` relates two carries, while
`WalkInv G C s` is indexed by one state and one carry.  This note records that half of the
merge's supply became a clause, and which half remains the wall.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkInduce
import LeanLLVM.Refinement.JsonStage2WalkRevolutionPrefix
import LeanLLVM.Refinement.JsonStage2WalkRevolutionScanRound

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The latch's and the exit's cells, where the scan's own lemmas do not reach

`latch462S_counter` and `latch462S_cond` (`JsonStage2WalkInduce`) read a latch built over
a *returning* visit's `scanLatchOut`; the latch this module consumes is the one the
landing's first edge builds (`hlastPrefixSeg`'s target), over the scan's entry state.  The
cells are the same three lattice pieces in the same order, so the peels are the same ones
with one layer fewer. -/

/-- The counter at a latch state: `landRhs457OutAt` binds `%q.0.i246` to the selected
index, and the two pivot cells above it bind other names. -/
theorem latch_counter (s : State) (idx : BitVec 64) (a q : Nat) (x : BitVec 8) :
    lookupName (Latch462S s idx a q x).env "%q.0.i246" = some (.int 64 idx) := by
  simp only [landRhs457OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The bound at a latch state is its entry state's: the lattice's six cells rebind
`%47`, `%arrayidx458.i`, `%q.0.i246`, `%Pivot106`, `%.off97` and `%SwitchLeaf98`, and
none of them is `%cond350.i`. -/
theorem latch_cond (s : State) (idx : BitVec 64) (a q : Nat) (x : BitVec 8) {c : Nat}
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c))) :
    lookupName (Latch462S s idx a q x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 c)) := by
  simp only [landRhs457OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hc

/-- The token record's register at the exit test's target: the test binds `%inc463.i` and
`%exitcond298.not`, and neither is `%t352.i`. -/
theorem scanExit_tok (s : State) (i c : Nat) {tok : Nat}
    (h : lookupName s.env "%t352.i" = some (.ptr tok)) :
    lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "if.end473.i").env
      "%t352.i" = some (.ptr tok) := by
  simp only [stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **The seam binds five cells and neither of the run's registers.**  Its `phi`, the
store's cell and the three literal tests are its own; the rest of the environment is the
state it was entered from. -/
theorem seamS_env_inc (s : State) (e : BitVec 64) (b8 : BitVec 8) (tok : Nat) :
    lookupName (seamS s e b8 tok).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the seam is its source's, for the same reason. -/
theorem seamS_env_nep (s : State) (e : BitVec 64) (b8 : BitVec 8) (tok : Nat) :
    lookupName (seamS s e b8 tok).env "%nep" = lookupName s.env "%nep" := by
  simp only [seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **The run's registers are the invariant's, read at the seam.**  `%inc.i` is
`WalkInv.inc_reg` and `%nep` is one of `walkStaticRegs`' pairs, and the seam binds neither —
so the segment's target invariant gives the endpoint `sl`'s cells, and they are not bundle
fields.  The run's *bound* is not a clause of the invariant either, so the run's producer
returns it beside the segment (`contWsRunF`). -/
theorem contWsSeamS_inc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sl : State)
    (k : Nat) (b8 : BitVec 8)
    (h : WalkInv G (ContSeamC C) (contWsSeamS C sl k b8)) :
    lookupName sl.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
  rw [← seamS_env_inc sl (BitVec.ofNat 64 k) b8 C.stage.tok]
  exact h.inc_reg

/-- `%nep` at the run's endpoint, from the same invariant. -/
theorem contWsSeamS_nep {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sl : State)
    (k : Nat) (b8 : BitVec 8)
    (h : WalkInv G (ContSeamC C) (contWsSeamS C sl k b8)) :
    lookupName sl.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
  rw [← seamS_env_nep sl (BitVec.ofNat 64 k) b8 C.stage.tok]
  exact h.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])

/-! ### The skip's byte, and the states its visits leave -/

/-- **The byte `scanB` reads is `wsByte`**, at an index the sign-extension leaves alone. -/
theorem scanB_ofNat {m0 : Mem} (G : WalkGeom m0) {p : Nat} (hp : p < 2 ^ 63) :
    scanB G (BitVec.ofNat 64 p) = wsByte G p := by
  simp only [scanB, wsByte, BitVec.signExtend_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The state `land.rhs.i`'s step leaves at index `p`: the byte's cell and its address. -/
def wsLandS {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) : State :=
  landRhsIOutAt G s (BitVec.ofNat 64 p) (wsByte G p)

/-- The state the skip's leaf leaves on its back edge — the latch's next state — at the
class the byte's first pivot selects.  The three arms are the three leaves. -/
def wsLeafS {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) : State :=
  if evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 1 then
    leafBlock43OutAt (nodeBlock52OutAt (wsLandS G s p) (wsX G p)) (wsX G p)
  else if evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 1 then
    scanLeafBlock46Out
      (scanNodeBlock50Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p)
  else
    scanLeafBlock48Out
      (scanNodeBlock48Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p)

/-- The state the skip leaves at `if.end372.i`: the leaf's cells, at the seam's block. -/
def wsStopS {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) : State :=
  { wsLeafS G s p with pc := "if.end372.i" }

/-! ### The three leaves' names for the leaf state -/

theorem wsLeafS_43 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 1) :
    wsLeafS G s p = leafBlock43OutAt (nodeBlock52OutAt (wsLandS G s p) (wsX G p)) (wsX G p) := by
  simp only [wsLeafS, h]
  simp

theorem wsLeafS_46 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 1) :
    wsLeafS G s p = scanLeafBlock46Out
      (scanNodeBlock50Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p) := by
  simp only [wsLeafS, h13, h32]
  rfl

theorem wsLeafS_48 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 0) :
    wsLeafS G s p = scanLeafBlock48Out
      (scanNodeBlock48Out (scanNodeBlock50In (wsLandS G s p) (wsX G p)) (wsX G p))
      (wsX G p) := by
  simp only [wsLeafS, h13, h32]
  rfl

/-! ### The landing state's cells -/

/-- `wsLandS`'s environment, named: the byte's two cells, then the counter's. -/
theorem wsLandS_env {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    (wsLandS G s p).env =
      ("%36", .int 8 (BitVec.ofNat 8 (wsByte G p).toNat)) ::
      ("%arrayidx367.i", .ptr (G.b + ((BitVec.ofNat 64 p).signExtend 64).toNat)) ::
      ("%ee.0.i238", .int 64 (BitVec.ofNat 64 p)) :: s.env := by
  simp only [wsLandS, landRhsIOutAt, stateAt, State.bindAll, State.bind, cells]

theorem wsLandS_ee {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    lookupName (wsLandS G s p).env "%ee.0.i238" =
      some (.int 64 (BitVec.ofNat 64 p)) := by
  rw [wsLandS_env, lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem wsLandS_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) {v : Nat}
    (h : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v))) :
    lookupName (wsLandS G s p).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
  rw [wsLandS_env, lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### A continuing visit, at the states the skip's own `def`s name

The atomic unit of the run: the latch's step and the dispatch's three links, from the
latch at `p` to the latch at `p + 1`, at `LeafBlock43`'s class.  The byte is the
document's, so the visit's hypotheses about it are this lemma's class premises. -/

theorem wsContinue43 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1)
    (hws0 : evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) :
    WalkSegment calls G C l { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by show v - (p + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hlt13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 1 := by
    rw [hb]; exact hlt13
  have hws' : evalICmp .ule
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0 := by
    rw [hb]; exact hws0
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 3 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hi₁
    have hseg := Seg.measure (calls := calls) (walkWhiteScanVisitSeg3_43
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hseg₁.inv' rfl hpre hin hv hpos hqn' halen hevlen hlt13' hws' hsc)
    rw [hb] at hseg
    rw [wsLeafS_43 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1) hlt13]
    simpa only [wsLandS, wsX, scanCarryLatchOf] using hseg
  exact hseg₁.trans hseg₂

/-- **A continuing visit at `LeafBlock46`'s class**, five links: the latch's step and the
four of the second pivot's first arm. -/
theorem wsContinue46 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 32) = 1)
    (hne13 : evalICmp .eq (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0) :
    WalkSegment calls G C l { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 5 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by show v - (p + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hge13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hge13
  have hlt32' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 1 := by
    rw [hb]; exact hlt32
  have hne13' : evalICmp .eq
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hne13
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hi₁
    have hseg := Seg.measure (calls := calls) (walkWhiteScanVisitSeg4_46
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hseg₁.inv' rfl hpre hin hv hpos hqn' halen hevlen hge13' hlt32' hne13' hsc)
    rw [hb] at hseg
    rw [wsLeafS_46 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      hge13 hlt32]
    simpa only [wsLandS, wsX, scanCarryLatchOf, scanCarryLeafBlock46, scanCarryNodeBlock50] using hseg
  exact hseg₁.trans hseg₂

/-- **A continuing visit at `LeafBlock48`'s class**, five links, the second pivot's second
arm. -/
theorem wsContinue48 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq (wsX G (p + 1)) (BitVec.ofNat 8 32) = 0) :
    WalkSegment calls G C l { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 5 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by show v - (p + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hge13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hge13
  have hge32' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 0 := by
    rw [hb]; exact hge32
  have hne32' : evalICmp .eq
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 0 := by
    rw [hb]; exact hne32
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "while.body370.i" }
      (wsLeafS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hi₁
    have hseg := Seg.measure (calls := calls) (walkWhiteScanVisitSeg4_48
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hseg₁.inv' rfl hpre hin hv hpos hqn' halen hevlen hge13' hge32' hne32' hsc)
    rw [hb] at hseg
    rw [wsLeafS_48 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      hge13 hge32]
    simpa only [wsLandS, wsX, scanCarryLatchOf, scanCarryLeafBlock48, scanCarryNodeBlock50] using hseg
  exact hseg₁.trans hseg₂

/-! ### The latch's step, as the facts its visit needs

`scanLatch_visit_at`'s target, pinned with the cells the dispatch's hypotheses read, so a
visit lemma states its four facts at the name rather than rebuilding them. -/

theorem wsLatchOut_facts {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (l : State) (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v) :
    WalkSegment calls G C l { C with block := "land.rhs.i" }
        (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") 1 ∧
      WalkInv G { C with block := "land.rhs.i" }
        (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") ∧
      lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
        "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
      lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) ∧
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
        some "while.body370.i" := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hinc₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%inc371.i" = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (p + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (p + 1))
          (BitVec.ofNat 64 v))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (p + 1)))] l.env) "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hpre : (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i").pre =
      some "while.body370.i" := by
    show some l.pc = some "while.body370.i"
    rw [hInv.pc_eq, hblock]
  have hland : WalkLocal { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") := by
    rw [WalkLocal.whitespaceLanded rfl]
    exact Or.inl ⟨p + 1, v, by
      have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
      show v - (p + 1) ≤ C.inner
      omega, hlt, hcw, hpre, hinc₁, hcond₁⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := l) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁ hi₁ hc₁
  exact ⟨hseg₁, hseg₁.inv', hi₁, hc₁, hpre⟩

/-! ### The dispatch's three links, at the leaf's exit arm

The visit of `walkWhiteScanVisitSeg3_43` with the leaf's own test set: the byte is `9` or
`10`, so `LeafBlock43` leaves for `if.end372.i` instead of the latch.  The local fact the
leaf's link takes is the latch's either way, so the only differences from the back-edge
statement are the arm and the target's block. -/

theorem wsVisit43Exit {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    Seg calls G C s
      { { { C with block := "NodeBlock52" } with block := "LeafBlock43" } with
        block := "if.end372.i" }
      { leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat) with pc := "if.end372.i" } 3 := by
  have hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1
      = some [G.bs.getD (e.signExtend 64).toNat 0] :=
    walkDoc_byte G C s hInv halen hevlen hqn
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.land_rhs_i_at G C s hInv hblock hpre hin hv hpos hread
  have hstep₁ : s₁ = landRhsIOutAt G s e (scanB G e) := by
    rw [hs₁]
    rfl
  rw [hstep₁] at hl₁
  have h36₁ : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells]
    rw [lookupName_cons_self]
  have h1 : evalOperand (landRhsIOutAt G s e (scanB G e)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₁
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock52_at G { C with block := "NodeBlock52" } (landRhsIOutAt G s e (scanB G e))
      hl₁.inv' rfl h1
  have hstep₂ : s₂ = nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₂]
    simp only [nodeBlock52OutAt, if_pos hlt13]
  rw [hstep₂] at hl₂
  rw [show (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "LeafBlock43" from if_pos hlt13] at hl₂
  have h36₂ : lookupName (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hsc₃ : ScanCount
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc
      [("%SwitchLeaf45", .int 1 (evalICmp .ule
          (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
       ("%.off44", .int 8 (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247))]
      (by
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact ⟨by simp, by simp⟩)
  have hloc : WalkLocal { { C with block := "NodeBlock52" } with block := "while.body370.i" }
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) := by
    rw [WalkLocal.whitespace rfl]
    exact hsc₃
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock43_at G _
      (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      hl₂.inv' (by simp) h36₂ hloc
  have hres : (if evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 then "if.end372.i" else "while.body370.i") = "if.end372.i" :=
    if_pos hws
  have hstep₃ : s₃ = { leafBlock43OutAt
      (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      (BitVec.ofNat 8 (scanB G e).toNat) with pc := "if.end372.i" } := by
    rw [hs₃]
    simp only [leafBlock43OutAt, hres]
  rw [hstep₃] at hl₃
  rw [hres] at hl₃
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.nil hl₃.inv')))

/-- **The dispatch's four links, at `LeafBlock46`'s exit arm.**  The test is `eq %36, 13`,
so a byte in `[13, 32)` leaves for `if.end372.i` only at `13`: the second pivot's first arm
and the leaf's exit, with the state's `pc` moved as `wsVisit43Exit` moves it. -/
theorem wsVisit46Exit {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1)
    (heq13 : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    Seg calls G C s
      { { { { C with block := "NodeBlock52" } with block := "NodeBlock50" } with
        block := "LeafBlock46" } with block := "if.end372.i" }
      { scanLeafBlock46Out
        (scanNodeBlock50Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
            (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat) with pc := "if.end372.i" } 4 := by
  -- the landing block
  have hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1
      = some [G.bs.getD (e.signExtend 64).toNat 0] :=
    walkDoc_byte G C s hInv halen hevlen hqn
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.land_rhs_i_at G C s hInv hblock hpre hin hv hpos hread
  have hstep₁ : s₁ = landRhsIOutAt G s e (scanB G e) := by
    rw [hs₁]
    rfl
  rw [hstep₁] at hl₁
  -- the first pivot, on the second arm
  have h36₁ : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells, State.bindAll, State.bind]
    block_lk
  have h1 : evalOperand (landRhsIOutAt G s e (scanB G e)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₁
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock52_at G { C with block := "NodeBlock52" }
      (landRhsIOutAt G s e (scanB G e)) hl₁.inv' rfl h1
  have hres₂ : (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "NodeBlock50" :=
    if_neg (by rw [hge13]; decide)
  have hstep₂ : s₂ = scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₂]
    simp only [scanNodeBlock50In, hres₂]
  rw [hstep₂] at hl₂
  rw [hres₂] at hl₂
  -- the second pivot, on its first arm
  have h36₂ : lookupName (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [State.bindAll, State.bind]
    block_lk
  have h2 : evalOperand (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₂
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock50_at G { { C with block := "NodeBlock52" } with block := "NodeBlock50" }
      (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      hl₂.inv' rfl h2
  have hres₃ : (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1
      then "LeafBlock46" else "LeafBlock48") = "LeafBlock46" := if_pos hlt32
  have hstep₃ : s₃ = scanNodeBlock50Out
      (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₃]
    simp only [scanNodeBlock50Out, hres₃]
  rw [hstep₃] at hl₃
  rw [hres₃] at hl₃
  -- the leaf, on its exit arm
  have h36₃ : lookupName (scanNodeBlock50Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot51", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 32))) ::
       ("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [State.bindAll, State.bind]
    block_lk
  have hsc₃ : ScanCount (scanNodeBlock50Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) "%ee.0.i238" "%cond350.i" C.inner := by
    refine ScanCount.bind (d := "%Pivot51")
      (v := .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32)))
      (ScanCount.bind (d := "%Pivot53")
        (v := .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13)))
        hsc (by decide) (by decide) (inner := C.inner))
      (by decide) (by decide) (inner := C.inner)
  have hsc₄ : ScanCount (scanLeafBlock46Out
      (scanNodeBlock50Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat))
      "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc₃
      [("%SwitchLeaf47", .int 1 (evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13)))]
      (by
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨by simp, by simp⟩)
  have hloc : WalkLocal { { { C with block := "NodeBlock52" } with block := "NodeBlock50" } with
      block := "while.body370.i" }
      (scanLeafBlock46Out
        (scanNodeBlock50Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat)) := by
    rw [WalkLocal.whitespace rfl]
    exact hsc₄
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock46_at G
      { { { C with block := "NodeBlock52" } with block := "NodeBlock50" } with block := "LeafBlock46" }
      (scanNodeBlock50Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat))
      hl₃.inv' rfl h36₃ hloc
  have hres₄ : (if evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1
      then "if.end372.i" else "while.body370.i") = "if.end372.i" :=
    if_pos heq13
  have hstep₄ : s₄ = { scanLeafBlock46Out
      (scanNodeBlock50Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat)
      with pc := "if.end372.i" } := by
    rw [hs₄]
    simp only [hres₄]
    rfl
  rw [hstep₄] at hl₄
  rw [hres₄] at hl₄
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄ (Seg.nil hl₄.inv'))))

/-- **The dispatch's four links, at `LeafBlock48`'s exit arm.**  The test is `eq %36, 32`,
so the second pivot's second arm leaves for `if.end372.i` only at `32`. -/
theorem wsVisit48Exit {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 0)
    (heq32 : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    Seg calls G C s
      { { { { C with block := "NodeBlock52" } with block := "NodeBlock50" } with
        block := "LeafBlock48" } with block := "if.end372.i" }
      { scanLeafBlock48Out
        (scanNodeBlock48Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
            (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat) with pc := "if.end372.i" } 4 := by
  -- the landing block
  have hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1
      = some [G.bs.getD (e.signExtend 64).toNat 0] :=
    walkDoc_byte G C s hInv halen hevlen hqn
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.land_rhs_i_at G C s hInv hblock hpre hin hv hpos hread
  have hstep₁ : s₁ = landRhsIOutAt G s e (scanB G e) := by
    rw [hs₁]
    rfl
  rw [hstep₁] at hl₁
  -- the first pivot, on the second arm
  have h36₁ : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells, State.bindAll, State.bind]
    block_lk
  have h1 : evalOperand (landRhsIOutAt G s e (scanB G e)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₁
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock52_at G { C with block := "NodeBlock52" }
      (landRhsIOutAt G s e (scanB G e)) hl₁.inv' rfl h1
  have hres₂ : (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "NodeBlock50" :=
    if_neg (by rw [hge13]; decide)
  have hstep₂ : s₂ = scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₂]
    simp only [scanNodeBlock50In, hres₂]
  rw [hstep₂] at hl₂
  rw [hres₂] at hl₂
  -- the second pivot, on its second arm
  have h36₂ : lookupName (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [State.bindAll, State.bind]
    block_lk
  have h2 : evalOperand (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₂
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock50_at G { { C with block := "NodeBlock52" } with block := "NodeBlock50" }
      (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      hl₂.inv' rfl h2
  have hres₃ : (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1
      then "LeafBlock46" else "LeafBlock48") = "LeafBlock48" := if_neg (by rw [hge32]; decide)
  have hstep₃ : s₃ = scanNodeBlock48Out
      (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₃]
    simp only [scanNodeBlock48Out, hres₃]
  rw [hstep₃] at hl₃
  rw [hres₃] at hl₃
  -- the leaf, on its exit arm
  have h36₃ : lookupName (scanNodeBlock48Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot51", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 32))) ::
       ("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [State.bindAll, State.bind]
    block_lk
  have hsc₃ : ScanCount (scanNodeBlock48Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) "%ee.0.i238" "%cond350.i" C.inner := by
    refine ScanCount.bind (d := "%Pivot51")
      (v := .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32)))
      (ScanCount.bind (d := "%Pivot53")
        (v := .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13)))
        hsc (by decide) (by decide) (inner := C.inner))
      (by decide) (by decide) (inner := C.inner)
  have hsc₄ : ScanCount (scanLeafBlock48Out
      (scanNodeBlock48Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat))
      "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc₃
      [("%SwitchLeaf49", .int 1 (evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 32)))]
      (by
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨by simp, by simp⟩)
  have hloc : WalkLocal { { { C with block := "NodeBlock52" } with block := "NodeBlock50" } with
      block := "while.body370.i" }
      (scanLeafBlock48Out
        (scanNodeBlock48Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat)) := by
    rw [WalkLocal.whitespace rfl]
    exact hsc₄
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock48_at G
      { { { C with block := "NodeBlock52" } with block := "NodeBlock50" } with block := "LeafBlock48" }
      (scanNodeBlock48Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat))
      hl₃.inv' rfl h36₃ hloc
  have hres₄ : (if evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1
      then "if.end372.i" else "while.body370.i") = "if.end372.i" :=
    if_pos heq32
  have hstep₄ : s₄ = { scanLeafBlock48Out
      (scanNodeBlock48Out
        (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat)
      with pc := "if.end372.i" } := by
    rw [hs₄]
    simp only [hres₄]
    rfl
  rw [hstep₄] at hl₄
  rw [hres₄] at hl₄
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.tail hl₄ (Seg.nil hl₄.inv'))))


/-! ### The visit that stops the skip: the latch's step and the leaf's exit

The run's last visit.  It is the continuing visit with the leaf's exit arm and the target's
`pc` at the seam, so each class has its lemma: `wsExit43` is four links and the `46`/`48`
twins are five.  The target is `wsStopS` — the leaf's own cells at `if.end372.i` — and the
carry is the run's, at the seam's block. -/

theorem wsExit43 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    WalkSegment calls G C l { C with block := "if.end372.i" }
      (wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  obtain ⟨hseg₁, hinv₁, hinc₁, hcond₁, hpre⟩ :=
    wsLatchOut_facts (calls := calls) G C l hInv hblock hi hc hcw hlt
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hlt13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 1 := by
    rw [hb]; exact hlt13
  have hws' : evalICmp .ule
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 := by
    rw [hb]; exact hws
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hstop : wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      = { leafBlock43OutAt
          (nodeBlock52OutAt (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
            "land.rhs.i") (p + 1)) (wsX G (p + 1))) (wsX G (p + 1)) with
        pc := "if.end372.i" } := by
    simp only [wsStopS, wsLeafS_43 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1) hlt13]
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "if.end372.i" }
      (wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 3 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hinc₁
    have hseg := Seg.measure (calls := calls) (wsVisit43Exit
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hinv₁ rfl hpre hin hv hpos hqn' halen hevlen hlt13' hws' hsc)
    rw [hb] at hseg
    rw [hstop]
    simpa only [wsLandS, wsX] using hseg
  exact hseg₁.trans hseg₂

theorem wsExit46 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 32) = 1)
    (heq13 : evalICmp .eq (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1) :
    WalkSegment calls G C l { C with block := "if.end372.i" }
      (wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 5 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  obtain ⟨hseg₁, hinv₁, hinc₁, hcond₁, hpre⟩ :=
    wsLatchOut_facts (calls := calls) G C l hInv hblock hi hc hcw hlt
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hge13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hge13
  have hlt32' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 1 := by
    rw [hb]; exact hlt32
  have heq13' : evalICmp .eq
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 1 := by
    rw [hb]; exact heq13
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hstop : wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      = { scanLeafBlock46Out
          (scanNodeBlock50Out
            (scanNodeBlock50In (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
              "land.rhs.i") (p + 1)) (wsX G (p + 1))) (wsX G (p + 1))) (wsX G (p + 1)) with
        pc := "if.end372.i" } := by
    simp only [wsStopS, wsLeafS_46 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1) hge13 hlt32]
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "if.end372.i" }
      (wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hinc₁
    have hseg := Seg.measure (calls := calls) (wsVisit46Exit
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hinv₁ rfl hpre hin hv hpos hqn' halen hevlen hge13' hlt32' heq13' hsc)
    rw [hb] at hseg
    rw [hstop]
    simpa only [wsLandS, wsX] using hseg
  exact hseg₁.trans hseg₂

theorem wsExit48 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    {p v : Nat} (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hlt : p + 1 < v)
    (hp63 : p + 1 < 2 ^ 63) (hqn : p + 1 < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 32) = 0)
    (heq32 : evalICmp .eq (wsX G (p + 1)) (BitVec.ofNat 8 32) = 1) :
    WalkSegment calls G C l { C with block := "if.end372.i" }
      (wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 5 := by
  have hSC : ScanCount l "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : v - p ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  obtain ⟨hseg₁, hinv₁, hinc₁, hcond₁, hpre⟩ :=
    wsLatchOut_facts (calls := calls) G C l hInv hblock hi hc hcw hlt
  have hb : scanB G (BitVec.ofNat 64 (p + 1)) = wsByte G (p + 1) := scanB_ofNat G hp63
  have hpos : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : ((BitVec.ofNat 64 (p + 1)).signExtend 64).toNat < G.n := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hge13' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 13) = 0 := by
    rw [hb]; exact hge13
  have hge32' : evalICmp .slt
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 0 := by
    rw [hb]; exact hge32
  have heq32' : evalICmp .eq
      (BitVec.ofNat 8 (scanB G (BitVec.ofNat 64 (p + 1))).toNat) (BitVec.ofNat 8 32) = 1 := by
    rw [hb]; exact heq32
  have hin : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    decide
  have hsc : ScanCount (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1)) "%ee.0.i238" "%cond350.i" C.inner :=
    ⟨p + 1, v, by omega, hlt, hcw,
      wsLandS_ee G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1),
      wsLandS_cond G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
        hcond₁⟩
  have hstop : wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)
      = { scanLeafBlock48Out
          (scanNodeBlock48Out
            (scanNodeBlock50In (wsLandS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
              "land.rhs.i") (p + 1)) (wsX G (p + 1))) (wsX G (p + 1))) (wsX G (p + 1)) with
        pc := "if.end372.i" } := by
    simp only [wsStopS, wsLeafS_48 G (scanLatchOut l "%inc371.i" "%exitcond.not" p v
      "land.rhs.i") (p + 1) hge13 hge32]
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      { C with block := "if.end372.i" }
      (wsStopS G (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i") (p + 1)) 4 := by
    have hv : evalOperand (scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
        (.reg "%inc371.i") = some (.int 64 (BitVec.ofNat 64 (p + 1))) := hinc₁
    have hseg := Seg.measure (calls := calls) (wsVisit48Exit
      (s := scanLatchOut l "%inc371.i" "%exitcond.not" p v "land.rhs.i")
      hinv₁ rfl hpre hin hv hpos hqn' halen hevlen hge13' hge32' heq32' hsc)
    rw [hb] at hseg
    rw [hstop]
    simpa only [wsLandS, wsX] using hseg
  exact hseg₁.trans hseg₂

/-! ### The run's indices

The run is a chain of latch states and one stop.  Each continuing visit moves the counter
by one, so the latch at counter `i + n` is the `n`-th application of `wsLeafS` to the same
head and the same bound: the recursion is the run's own shape, and the induction below is
`Nat.rec` on it.  The stop is indexed by the counter it stops at, `match k - i`.

`v` — `%cond350.i`, the entry's end — does not move across the skip: no leaf rebinds it, so
every visit is stated at the same `v`. -/

/-- The latch at counter `i + n`: `n` visits past the head state `l`. -/
def wsLatchAt {m0 : Mem} (G : WalkGeom m0) (l : State) (i v : Nat) : Nat → State
  | 0 => l
  | n + 1 => wsLeafS G (scanLatchOut (wsLatchAt G l i v n) "%inc371.i" "%exitcond.not"
      (i + n) v "land.rhs.i") (i + n + 1)

/-- The state the skip stops at counter `k`: the leaf's cells at `if.end372.i`, entered from
the latch at `k - 1`.  The `0` arm is the head state itself, reached only when `k ≤ i`,
which the run's hypotheses exclude. -/
def wsStopAt {m0 : Mem} (G : WalkGeom m0) (l : State) (i v k : Nat) : State :=
  match k - i with
  | 0 => l
  | n + 1 => wsStopS G (scanLatchOut (wsLatchAt G l i v n) "%inc371.i" "%exitcond.not"
      (i + n) v "land.rhs.i") (i + n + 1)

/-! ### The byte's class

A visit is decided by the byte it reads — the document's byte at the index the latch's
increment names — and the three leaves split it three ways: `LeafBlock43` for bytes below
`13` (its `ule` test separates `9`/`10`), `LeafBlock46` for `[13, 32)` (its `eq` test
separates `13`) and `LeafBlock48` for `32` and above (its `eq` test separates `32`).  The
same disjunction serves the continuing and the stopping visit; which arm it is decides
which of `wsContinue*` or `wsExit*` applies. -/

/-- The byte at `q` takes one leaf's back edge: the skip continues. -/
def wsCont {m0 : Mem} (G : WalkGeom m0) (q : Nat) : Prop :=
  (evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (wsX G q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) ∨
    (evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsX G q) (BitVec.ofNat 8 32) = 1 ∧
      evalICmp .eq (wsX G q) (BitVec.ofNat 8 13) = 0) ∨
    (evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsX G q) (BitVec.ofNat 8 32) = 0 ∧
      evalICmp .eq (wsX G q) (BitVec.ofNat 8 32) = 0)

/-- The byte at `q` leaves its leaf for `if.end372.i`: the skip stops. -/
def wsStop {m0 : Mem} (G : WalkGeom m0) (q : Nat) : Prop :=
  (evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (wsX G q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
    (evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsX G q) (BitVec.ofNat 8 32) = 1 ∧
      evalICmp .eq (wsX G q) (BitVec.ofNat 8 13) = 1) ∨
    (evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 0 ∧
      evalICmp .slt (wsX G q) (BitVec.ofNat 8 32) = 0 ∧
      evalICmp .eq (wsX G q) (BitVec.ofNat 8 32) = 1)

/-! ### The cells the leaf states carry

The induction's strengthened hypothesis is `WalkSegment` plus the invariant plus these two
cells — a visit's *input* — so the step needs them at the state it reaches.  Both are the
landing's: `landRhsIOutAt` binds `%ee.0.i238` to the incremented counter, and no block from
the landing to a leaf rebinds `%cond350.i`, so the bound crosses the visit untouched.  The
peels differ only in how many cells the class's leaf adds. -/

theorem wsLeafS_43_ee {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 1) :
    lookupName (wsLeafS G s p).env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)) := by
  rw [wsLeafS_43 G s p h13]
  simp only [leafBlock43OutAt, nodeBlock52OutAt, landRhsIOutAt, stateAt, State.bind,
    State.bindAll, cells, wsLandS]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem wsLeafS_43_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p v : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 1)
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v))) :
    lookupName (wsLeafS G s p).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
  rw [wsLeafS_43 G s p h13]
  simp only [leafBlock43OutAt, nodeBlock52OutAt, landRhsIOutAt, stateAt, State.bind,
    State.bindAll, cells, wsLandS]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact hc

theorem wsLeafS_46_ee {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 1) :
    lookupName (wsLeafS G s p).env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)) := by
  rw [wsLeafS_46 G s p h13 h32]
  simp only [scanNodeBlock50In, landRhsIOutAt,
    stateAt, State.bind, State.bindAll, cells, wsLandS]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem wsLeafS_46_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p v : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 1)
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v))) :
    lookupName (wsLeafS G s p).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
  rw [wsLeafS_46 G s p h13 h32]
  simp only [scanNodeBlock50In, landRhsIOutAt,
    stateAt, State.bind, State.bindAll, cells, wsLandS]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact hc

theorem wsLeafS_48_ee {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 0) :
    lookupName (wsLeafS G s p).env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)) := by
  rw [wsLeafS_48 G s p h13 h32]
  simp only [scanNodeBlock50In, landRhsIOutAt,
    stateAt, State.bind, State.bindAll, cells, wsLandS]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem wsLeafS_48_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p v : Nat)
    (h13 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 13) = 0)
    (h32 : evalICmp .slt (wsX G p) (BitVec.ofNat 8 32) = 0)
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v))) :
    lookupName (wsLeafS G s p).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)) := by
  rw [wsLeafS_48 G s p h13 h32]
  simp only [scanNodeBlock50In, landRhsIOutAt,
    stateAt, State.bind, State.bindAll, cells, wsLandS]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact hc

/-! ### The run

The induction, over the only index that decreases: the number of continuing visits left,
`k - 1 - (i + d)` at the `d`-th latch.  The statement is the strengthened one — the segment,
its target's invariant, and the two cells every visit reads — because a step's input is
exactly what the previous step left, and a segment's `inv'` alone does not name the cells.

The count is a bound and not an equality: the byte's class decides whether a visit costs
four links or five, so the run from the latch at `i` to the stop at `k` is at most
`5·(k - i)` links — five a continuing byte and five at the exit — and the induction's own
bound is `5·r + 5` at `r = k - 1 - (i + d)`.

The premises are the document's, per index: `hcls` says every byte the skip reads before
`k` continues it, `hstop` says the byte at `k` ends it, and `hpos`/`hqn` place every read
inside the byte's 63 bits and inside the document. -/

theorem wsRun_go {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (l : State) {i v k : Nat}
    (hcw : v < 2 ^ 64) (hik : i < k) (hkv : k < v)
    (hcls : ∀ q, i < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, i < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, i < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap) :
    ∀ r d, k - 1 - (i + d) = r → i + d < k →
      WalkInv G { C with block := "while.body370.i" } (wsLatchAt G l i v d) →
      lookupName (wsLatchAt G l i v d).env "%ee.0.i238" =
        some (.int 64 (BitVec.ofNat 64 (i + d))) →
      lookupName (wsLatchAt G l i v d).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v)) →
      ∃ n, n ≤ 5 * r + 5 ∧
        WalkSegment calls G { C with block := "while.body370.i" } (wsLatchAt G l i v d)
          { C with block := "if.end372.i" } (wsStopAt G l i v k) n ∧
        WalkInv G { C with block := "if.end372.i" } (wsStopAt G l i v k) ∧
        lookupName (wsStopAt G l i v k).env "%ee.0.i238" =
          some (.int 64 (BitVec.ofNat 64 k)) ∧
        lookupName (wsStopAt G l i v k).env "%cond350.i" =
          some (.int 64 (BitVec.ofNat 64 v))
  | 0, d, hr, hltd, hinv, hee, hcond => by
    let s : State := scanLatchOut (wsLatchAt G l i v d) "%inc371.i" "%exitcond.not"
      (i + d) v "land.rhs.i"
    have hid : i + d + 1 = k := by omega
    have hki : k - i = d + 1 := by omega
    have hstopEq : wsStopAt G l i v k = wsStopS G s (i + d + 1) := by
      simp only [wsStopAt, hki]
      rfl
    rw [hstopEq]
    have hpos' : i + d + 1 < 2 ^ 63 := by
      have := hpos k (by omega) (by omega); omega
    have hqn' : i + d + 1 < G.n := by
      have := hqn k (by omega) (by omega); omega
    rcases hstop with ⟨h13, hws⟩ | ⟨h13, h32, heq⟩ | ⟨h13, h32, heq⟩
    · rw [← hid] at h13 hws
      have hseg := wsExit43 (calls := calls) G { C with block := "while.body370.i" }
        (wsLatchAt G l i v d) hinv rfl hee hcond hcw (by omega) hpos' hqn' halen hevlen h13 hws
      refine ⟨4, by simp, hseg, hseg.inv', ?_, ?_⟩
      · simpa only [wsStopS, ← hid] using wsLeafS_43_ee G s (i + d + 1) h13
      · simpa only [wsStopS] using wsLeafS_43_cond G s (i + d + 1) v h13 hcond
    · rw [← hid] at h13 h32 heq
      have hseg := wsExit46 (calls := calls) G { C with block := "while.body370.i" }
        (wsLatchAt G l i v d) hinv rfl hee hcond hcw (by omega) hpos' hqn' halen hevlen h13 h32 heq
      refine ⟨5, by simp, hseg, hseg.inv', ?_, ?_⟩
      · simpa only [wsStopS, ← hid] using wsLeafS_46_ee G s (i + d + 1) h13 h32
      · simpa only [wsStopS] using wsLeafS_46_cond G s (i + d + 1) v h13 h32 hcond
    · rw [← hid] at h13 h32 heq
      have hseg := wsExit48 (calls := calls) G { C with block := "while.body370.i" }
        (wsLatchAt G l i v d) hinv rfl hee hcond hcw (by omega) hpos' hqn' halen hevlen h13 h32 heq
      refine ⟨5, by simp, hseg, hseg.inv', ?_, ?_⟩
      · simpa only [wsStopS, ← hid] using wsLeafS_48_ee G s (i + d + 1) h13 h32
      · simpa only [wsStopS] using wsLeafS_48_cond G s (i + d + 1) v h13 h32 hcond
  | r + 1, d, hr, hltd, hinv, hee, hcond => by
    let s : State := scanLatchOut (wsLatchAt G l i v d) "%inc371.i" "%exitcond.not"
      (i + d) v "land.rhs.i"
    have hd : i + d + 1 < k := by omega
    have hlatch : wsLatchAt G l i v (d + 1) = wsLeafS G s (i + d + 1) := rfl
    have hpos' : i + d + 1 < 2 ^ 63 := hpos (i + d + 1) (by omega) (by omega)
    have hqn' : i + d + 1 < G.n := hqn (i + d + 1) (by omega) (by omega)
    have hnext : k - 1 - (i + (d + 1)) = r := by omega
    rcases hcls (i + d + 1) (by omega) hd with ⟨h13, hws⟩ | ⟨h13, h32, hne⟩
      | ⟨h13, h32, hne⟩
    · have hseg₁ := wsContinue43 (calls := calls) G { C with block := "while.body370.i" }
        (wsLatchAt G l i v d) hinv rfl hee hcond hcw (by omega) hpos' hqn' halen hevlen h13 hws
      obtain ⟨n, hn, hseg₂, hinv₂, hee₂, hcond₂⟩ :=
        wsRun_go (calls := calls) G C l hcw hik hkv hcls hstop hpos hqn halen hevlen
          r (d + 1) hnext (by omega)
          (by rw [hlatch]; exact hseg₁.inv')
          (by rw [hlatch]; exact wsLeafS_43_ee G s (i + d + 1) h13)
          (by rw [hlatch]; exact wsLeafS_43_cond G s (i + d + 1) v h13 hcond)
      rw [hlatch] at hseg₂
      exact ⟨4 + n, by omega, hseg₁.trans hseg₂, hinv₂, hee₂, hcond₂⟩
    · have hseg₁ := wsContinue46 (calls := calls) G { C with block := "while.body370.i" }
        (wsLatchAt G l i v d) hinv rfl hee hcond hcw (by omega) hpos' hqn' halen hevlen h13 h32 hne
      obtain ⟨n, hn, hseg₂, hinv₂, hee₂, hcond₂⟩ :=
        wsRun_go (calls := calls) G C l hcw hik hkv hcls hstop hpos hqn halen hevlen
          r (d + 1) hnext (by omega)
          (by rw [hlatch]; exact hseg₁.inv')
          (by rw [hlatch]; exact wsLeafS_46_ee G s (i + d + 1) h13 h32)
          (by rw [hlatch]; exact wsLeafS_46_cond G s (i + d + 1) v h13 h32 hcond)
      rw [hlatch] at hseg₂
      exact ⟨5 + n, by omega, hseg₁.trans hseg₂, hinv₂, hee₂, hcond₂⟩
    · have hseg₁ := wsContinue48 (calls := calls) G { C with block := "while.body370.i" }
        (wsLatchAt G l i v d) hinv rfl hee hcond hcw (by omega) hpos' hqn' halen hevlen h13 h32 hne
      obtain ⟨n, hn, hseg₂, hinv₂, hee₂, hcond₂⟩ :=
        wsRun_go (calls := calls) G C l hcw hik hkv hcls hstop hpos hqn halen hevlen
          r (d + 1) hnext (by omega)
          (by rw [hlatch]; exact hseg₁.inv')
          (by rw [hlatch]; exact wsLeafS_48_ee G s (i + d + 1) h13 h32)
          (by rw [hlatch]; exact wsLeafS_48_cond G s (i + d + 1) v h13 h32 hcond)
      rw [hlatch] at hseg₂
      exact ⟨5 + n, by omega, hseg₁.trans hseg₂, hinv₂, hee₂, hcond₂⟩

/-! ### The run, from its head latch to the stop

The induction at `d = 0`, with the head state's carry named: `C.block = "while.body370.i"` is
what makes `{ C with block := "while.body370.i" }` the same carry, so the segment is stated at
`C` and the endpoint at `{ C with block := "if.end372.i" }`.

The bound is the count: `k - i` visits — the latch at `i` reads `i + 1` and the stop's visit
is sourced at `k - 1` — at five links each at most, so `n ≤ 5·(k - i)`.  The statement is
existential because the classes differ in cost: `∃ n, n ≤ 5·(k - i) ∧ WalkSegment … n`. -/

theorem wsRun {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (l : State)
    {i v k : Nat}
    (hInv : WalkInv G C l) (hblock : C.block = "while.body370.i")
    (hi : lookupName l.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName l.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v)))
    (hcw : v < 2 ^ 64) (hik : i < k) (hkv : k < v)
    (hcls : ∀ q, i < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, i < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, i < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap) :
    ∃ n, n ≤ 5 * (k - i) ∧
      WalkSegment calls G C l { C with block := "if.end372.i" } (wsStopAt G l i v k) n ∧
      WalkInv G { C with block := "if.end372.i" } (wsStopAt G l i v k) ∧
      lookupName (wsStopAt G l i v k).env "%ee.0.i238" =
        some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName (wsStopAt G l i v k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v)) := by
  have hCw : ({ C with block := "while.body370.i" } : WalkCarry G) = C := by
    rw [← hblock]
  obtain ⟨n, hn, hseg, hinv, hee, hcond⟩ :=
    wsRun_go (calls := calls) G C l hcw hik hkv hcls hstop hpos hqn halen hevlen
      (k - 1 - i) 0 rfl hik (by rw [hCw]; exact hInv) hi hc
  refine ⟨n, by omega, ?_, ?_, hee, hcond⟩
  · rw [hCw] at hseg; exact hseg
  · exact hinv



/-! ### The seam: `if.end372.i` → the class-C span's entry

`wsRun`'s endpoint is `wsStopAt G l i v k` at the block `if.end372.i`; the seam's step is
that block's run at the `phi` the skip's leaf installed.  The `phi` selects `%ee.0.i238`
on the three leaves' edges, and the run's target cell is `k`, so the stored end is
`ofNat 64 k`. -/

/-- **The seam link**: `if.end372.i`'s step, from the run's endpoint to the class-C span's
entry at the run class's seam.  The carried triple names the target, so the segment's
`inv'` is the seam's own invariant and the class-C span reads it. -/
theorem wsSeamSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) {k : Nat} {b8 : BitVec 8} {p : String}
    (hInv : WalkInv G { C with block := "if.end372.i" } sl)
    (hpre : sl.pre = some p)
    (hin : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some (.reg "%ee.0.i238"))
    (hi : lookupName sl.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 k)))
    (hend : lookupName sl.env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8 : lookupName sl.env "%8" = some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    WalkSegment calls G { C with block := "if.end372.i" } sl (ContSeamC C)
      (contWsSeamS C sl k b8) 1 := by
  have hv : evalOperand sl (.reg "%ee.0.i238") =
      some (.int 64 (BitVec.ofNat 64 k)) := hi
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.if_end372_i_at (calls := calls) (G := G)
      (C := { C with block := "if.end372.i" }) (s := sl) hInv rfl hpre hin hv hend h8 hbit
  rw [hs] at hl
  exact WalkSegment.of_link hl

/-! ### The first visit: the preheader's edge and the skip's first byte

`wsRun` starts at the latch, whose first read is `i + 1`.  The byte at `i` therefore sits
one visit outside it, and it is this piece: the preheader's `br` (one link, the
`ScanEntered` local at `land.rhs.i`) and the visit through the fold's leaf (three links at
`LeafBlock43`'s class, four at `46`/`48`'s).  The visit's source is the `land.rhs.i` state
the preheader leaves; `wsLeafS` is exactly its target. -/

/-- **The first visit at `LeafBlock43`'s class** — the entry's own byte continues the
token — four links from the preheader's state to the latch at counter `i`. -/
theorem wsFirstSeg43 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (pre : State)
    (hInv : WalkInv G { C with block := "land.rhs.i.preheader" } pre)
    (hpc : pre.pc = "land.rhs.i.preheader")
    (hsc : ScanEntered { pre with pc := "land.rhs.i", pre := some pre.pc }
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner)
    {i : Nat} {e : BitVec 64}
    (hev : evalOperand (landRhsPreheaderOutAt pre) (.reg "%idxprom.i") = some (.int 64 e))
    (he : e = BitVec.ofNat 64 i)
    (hi63 : i < 2 ^ 63) (hqn : i < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (wsX G i) (BitVec.ofNat 8 13) = 1)
    (hws0 : evalICmp .ule (wsX G i + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0)
    (hsc2 : ScanCount (landRhsIOutAt G (landRhsPreheaderOutAt pre) e (scanB G e))
      "%ee.0.i238" "%cond350.i" C.inner) :
    WalkSegment calls G { C with block := "land.rhs.i.preheader" } pre
      { C with block := "while.body370.i" } (wsLeafS G (landRhsPreheaderOutAt pre) i) 4 := by
  have hloc : WalkLocal { C with block := "land.rhs.i" }
      { pre with pc := "land.rhs.i", pre := some pre.pc } := by
    rw [WalkLocal.whitespaceLanded (C := { C with block := "land.rhs.i" }) rfl]
    exact Or.inr hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.land_rhs_i_preheader_at (calls := calls) G
      { C with block := "land.rhs.i.preheader" } pre hInv rfl hloc
  have hs' : s' = landRhsPreheaderOutAt pre := hs
  rw [hs'] at hl
  have hpre : (landRhsPreheaderOutAt pre).pre = some "land.rhs.i.preheader" := by
    show some pre.pc = some "land.rhs.i.preheader"
    rw [hpc]
  have hin : phiIncoming "land.rhs.i.preheader"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%idxprom.i") := by
    decide
  have hpos : (e.signExtend 64).toNat < 2 ^ 63 := by
    rw [he, BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : (e.signExtend 64).toNat < G.n := by
    rw [he, BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hb : scanB G e = wsByte G i := by
    rw [he]; exact scanB_ofNat G hi63
  have hlt13' : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 13) = 1 := by rw [hb]; exact hlt13
  have hws' : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0 := by rw [hb]; exact hws0
  have hseg2 := walkWhiteScanVisitSeg3_43 (calls := calls) hl.inv' rfl hpre hin hev hpos hqn'
    halen hevlen hlt13' hws' hsc2
  rw [he] at hseg2
  rw [scanB_ofNat G hi63] at hseg2
  have hseg2' : WalkSegment calls G { C with block := "land.rhs.i" }
      (landRhsPreheaderOutAt pre) { C with block := "while.body370.i" }
      (wsLeafS G (landRhsPreheaderOutAt pre) i) 3 := by
    rw [wsLeafS_43 G (landRhsPreheaderOutAt pre) i hlt13]
    simpa only [wsLandS, wsX, scanCarryLatchOf] using Seg.measure hseg2
  exact (WalkSegment.of_link hl).trans hseg2'

/-- **The first visit at `LeafBlock46`'s class** — five links, the second pivot's first
arm. -/
theorem wsFirstSeg46 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (pre : State)
    (hInv : WalkInv G { C with block := "land.rhs.i.preheader" } pre)
    (hpc : pre.pc = "land.rhs.i.preheader")
    (hsc : ScanEntered { pre with pc := "land.rhs.i", pre := some pre.pc }
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner)
    {i : Nat} {e : BitVec 64}
    (hev : evalOperand (landRhsPreheaderOutAt pre) (.reg "%idxprom.i") = some (.int 64 e))
    (he : e = BitVec.ofNat 64 i)
    (hi63 : i < 2 ^ 63) (hqn : i < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G i) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (wsX G i) (BitVec.ofNat 8 32) = 1)
    (hne13 : evalICmp .eq (wsX G i) (BitVec.ofNat 8 13) = 0)
    (hsc2 : ScanCount (landRhsIOutAt G (landRhsPreheaderOutAt pre) e (scanB G e))
      "%ee.0.i238" "%cond350.i" C.inner) :
    WalkSegment calls G { C with block := "land.rhs.i.preheader" } pre
      { C with block := "while.body370.i" } (wsLeafS G (landRhsPreheaderOutAt pre) i) 5 := by
  have hloc : WalkLocal { C with block := "land.rhs.i" }
      { pre with pc := "land.rhs.i", pre := some pre.pc } := by
    rw [WalkLocal.whitespaceLanded (C := { C with block := "land.rhs.i" }) rfl]
    exact Or.inr hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.land_rhs_i_preheader_at (calls := calls) G
      { C with block := "land.rhs.i.preheader" } pre hInv rfl hloc
  have hs' : s' = landRhsPreheaderOutAt pre := hs
  rw [hs'] at hl
  have hpre : (landRhsPreheaderOutAt pre).pre = some "land.rhs.i.preheader" := by
    show some pre.pc = some "land.rhs.i.preheader"
    rw [hpc]
  have hin : phiIncoming "land.rhs.i.preheader"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%idxprom.i") := by
    decide
  have hpos : (e.signExtend 64).toNat < 2 ^ 63 := by
    rw [he, BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : (e.signExtend 64).toNat < G.n := by
    rw [he, BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hb : scanB G e = wsByte G i := by
    rw [he]; exact scanB_ofNat G hi63
  have hge13' : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 13) = 0 := by rw [hb]; exact hge13
  have hlt32' : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 32) = 1 := by rw [hb]; exact hlt32
  have hne13' : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 13) = 0 := by rw [hb]; exact hne13
  have hseg2 := walkWhiteScanVisitSeg4_46 (calls := calls) hl.inv' rfl hpre hin hev hpos hqn'
    halen hevlen hge13' hlt32' hne13' hsc2
  rw [he] at hseg2
  rw [scanB_ofNat G hi63] at hseg2
  have hseg2' : WalkSegment calls G { C with block := "land.rhs.i" }
      (landRhsPreheaderOutAt pre) { C with block := "while.body370.i" }
      (wsLeafS G (landRhsPreheaderOutAt pre) i) 4 := by
    rw [wsLeafS_46 G (landRhsPreheaderOutAt pre) i hge13 hlt32]
    simpa only [wsLandS, wsX, scanCarryLatchOf, scanCarryLeafBlock46, scanCarryNodeBlock50]
      using Seg.measure hseg2
  exact (WalkSegment.of_link hl).trans hseg2'

/-- **The first visit at `LeafBlock48`'s class** — five links, the second pivot's second
arm. -/
theorem wsFirstSeg48 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (pre : State)
    (hInv : WalkInv G { C with block := "land.rhs.i.preheader" } pre)
    (hpc : pre.pc = "land.rhs.i.preheader")
    (hsc : ScanEntered { pre with pc := "land.rhs.i", pre := some pre.pc }
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner)
    {i : Nat} {e : BitVec 64}
    (hev : evalOperand (landRhsPreheaderOutAt pre) (.reg "%idxprom.i") = some (.int 64 e))
    (he : e = BitVec.ofNat 64 i)
    (hi63 : i < 2 ^ 63) (hqn : i < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (wsX G i) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (wsX G i) (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq (wsX G i) (BitVec.ofNat 8 32) = 0)
    (hsc2 : ScanCount (landRhsIOutAt G (landRhsPreheaderOutAt pre) e (scanB G e))
      "%ee.0.i238" "%cond350.i" C.inner) :
    WalkSegment calls G { C with block := "land.rhs.i.preheader" } pre
      { C with block := "while.body370.i" } (wsLeafS G (landRhsPreheaderOutAt pre) i) 5 := by
  have hloc : WalkLocal { C with block := "land.rhs.i" }
      { pre with pc := "land.rhs.i", pre := some pre.pc } := by
    rw [WalkLocal.whitespaceLanded (C := { C with block := "land.rhs.i" }) rfl]
    exact Or.inr hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.land_rhs_i_preheader_at (calls := calls) G
      { C with block := "land.rhs.i.preheader" } pre hInv rfl hloc
  have hs' : s' = landRhsPreheaderOutAt pre := hs
  rw [hs'] at hl
  have hpre : (landRhsPreheaderOutAt pre).pre = some "land.rhs.i.preheader" := by
    show some pre.pc = some "land.rhs.i.preheader"
    rw [hpc]
  have hin : phiIncoming "land.rhs.i.preheader"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%idxprom.i") := by
    decide
  have hpos : (e.signExtend 64).toNat < 2 ^ 63 := by
    rw [he, BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hqn' : (e.signExtend 64).toNat < G.n := by
    rw [he, BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hqn
  have hb : scanB G e = wsByte G i := by
    rw [he]; exact scanB_ofNat G hi63
  have hge13' : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 13) = 0 := by rw [hb]; exact hge13
  have hge32' : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 32) = 0 := by rw [hb]; exact hge32
  have hne32' : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat)
      (BitVec.ofNat 8 32) = 0 := by rw [hb]; exact hne32
  have hseg2 := walkWhiteScanVisitSeg4_48 (calls := calls) hl.inv' rfl hpre hin hev hpos hqn'
    halen hevlen hge13' hge32' hne32' hsc2
  rw [he] at hseg2
  rw [scanB_ofNat G hi63] at hseg2
  have hseg2' : WalkSegment calls G { C with block := "land.rhs.i" }
      (landRhsPreheaderOutAt pre) { C with block := "while.body370.i" }
      (wsLeafS G (landRhsPreheaderOutAt pre) i) 4 := by
    rw [wsLeafS_48 G (landRhsPreheaderOutAt pre) i hge13 hge32]
    simpa only [wsLandS, wsX, scanCarryLatchOf, scanCarryLeafBlock48, scanCarryNodeBlock50]
      using Seg.measure hseg2
  exact (WalkSegment.of_link hl).trans hseg2'

/-! ### The entry dispatch: `contLandS` → the preheader by `%35`'s class

`%35` is the byte before the entry's end.  On the run class it is one of the four
whitespace bytes, so the leaf the three pivots reach takes its **true** arm and the walk
enters the skip at `land.rhs.i.preheader`.  The arms differ in the cells the pivots and
the leaf bound, and hence in the state the preheader is entered at — the class-indexed
source the run's endpoint carries as data.  `LeafBlock33`'s arm is two links,
`LeafBlock35`'s and `LeafBlock37`'s three. -/

/-- The state `NodeBlock39` leaves at the class that takes `%35 ≥ 32`: the pivot's cell,
at `LeafBlock37`. -/
def contP37S {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((contP41S C s x inc nep ep v ix b35).bind "%Pivot40"
      (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock37", pre := some (contP41S C s x inc nep ep v ix b35).pc }

/-- The state `LeafBlock35` leaves on the arm its `%35 = 13` test takes. -/
def leafBlock35OutAt (s : State) (x : BitVec 8) : State :=
  { (s.bind "%SwitchLeaf36" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 13)))) with
    pc := "land.rhs.i.preheader", pre := some s.pc }

/-- The state `LeafBlock37` leaves on the arm its `%35 = 32` test takes. -/
def leafBlock37OutAt (s : State) (x : BitVec 8) : State :=
  { (s.bind "%SwitchLeaf38" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 32)))) with
    pc := "land.rhs.i.preheader", pre := some s.pc }

/-- `%35` at the byte's second pivot on its second arm. -/
theorem contP37S_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contP37S C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contP37S, contP41S, contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- **The entry dispatch at `LeafBlock33`'s class**: `%35 < 13` and the `ule` test true —
two links from the whitespace check's target to the preheader. -/
theorem wsEntry33 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8)
    (hInv : WalkInv G (ContAC₄ C) (contLandS C s x inc nep ep v ix b35))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    WalkSegment calls G (ContAC₄ C) (contLandS C s x inc nep ep v ix b35)
      { C with block := "land.rhs.i.preheader" }
      (leafBlock33OutAt
        (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
        (cont35 b35)) 2 := by
  have h35 : evalOperand (contLandS C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandS_35 C s x inc nep ep v ix b35
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hInv rfl h35
  have hres : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "LeafBlock33" := if_pos hb13
  have hst : s₁ = nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35) := by
    rw [hs₁, hres]; rfl
  rw [hst] at hl₁
  rw [hres] at hl₁
  have h35' : lookupName
      (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35)).env "%35" =
      some (.int 8 (cont35 b35)) := by
    show lookupName (("%Pivot42", .int 1 (evalICmp .slt (cont35 b35)
      (BitVec.ofNat 8 13))) :: (contLandS C s x inc nep ep v ix b35).env) "%35" =
      some (.int 8 (cont35 b35))
    rw [lookupName_cons_ne _ _ (by decide)]
    exact contLandS_35 C s x inc nep ep v ix b35
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.LeafBlock33_at (calls := calls) G { ContAC₄ C with block := "LeafBlock33" }
      (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
      hl₁.inv' rfl h35'
  have hres2 : (if evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 then "land.rhs.i.preheader" else "if.end372.i") =
      "land.rhs.i.preheader" := if_pos hws
  have hst2 : s₂ = leafBlock33OutAt
      (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
      (cont35 b35) := by
    rw [hs₂, hres2]; rfl
  rw [hst2] at hl₂
  rw [hres2] at hl₂
  exact (WalkSegment.of_link hl₁).trans (WalkSegment.of_link hl₂)

/-- **The entry dispatch at `LeafBlock35`'s class**: `13 ≤ %35 < 32` and `%35 = 13` true —
three links from the whitespace check's target to the preheader. -/
theorem wsEntry35 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8)
    (hInv : WalkInv G (ContAC₄ C) (contLandS C s x inc nep ep v ix b35))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbq13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) :
    WalkSegment calls G (ContAC₄ C) (contLandS C s x inc nep ep v ix b35)
      { C with block := "land.rhs.i.preheader" }
      (leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35)) 3 := by
  have h35 : evalOperand (contLandS C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandS_35 C s x inc nep ep v ix b35
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hInv rfl h35
  have hres : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
  have hst : s₁ = contP41S C s x inc nep ep v ix b35 := by
    rw [hs₁, hres]; rfl
  rw [hst] at hl₁
  rw [hres] at hl₁
  have h35b : evalOperand (contP41S C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP41S_35 C s x inc nep ep v ix b35
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock39_at (calls := calls) G (ContAC₅ C)
      (contP41S C s x inc nep ep v ix b35) hl₁.inv' rfl h35b
  have hres2 : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
      "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := if_pos hb32
  have hst2 : s₂ = contP39S C s x inc nep ep v ix b35 := by
    rw [hs₂, hres2]; rfl
  rw [hst2] at hl₂
  rw [hres2] at hl₂
  have h35c : evalOperand (contP39S C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP39S_35 C s x inc nep ep v ix b35
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock35_at (calls := calls) G (ContAC₆ C)
      (contP39S C s x inc nep ep v ix b35) hl₂.inv' rfl h35c
  have hres3 : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "land.rhs.i.preheader" else "if.end372.i") = "land.rhs.i.preheader" :=
    if_pos hbq13
  have hst3 : s₃ = leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35) := by
    rw [hs₃, hres3]; rfl
  rw [hst3] at hl₃
  rw [hres3] at hl₃
  exact ((WalkSegment.of_link hl₁).trans (WalkSegment.of_link hl₂)).trans
    (WalkSegment.of_link hl₃)

/-- **The entry dispatch at `LeafBlock37`'s class**: `%35 ≥ 32` and `%35 = 32` true —
three links from the whitespace check's target to the preheader. -/
theorem wsEntry37 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8)
    (hInv : WalkInv G (ContAC₄ C) (contLandS C s x inc nep ep v ix b35))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbq32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1) :
    WalkSegment calls G (ContAC₄ C) (contLandS C s x inc nep ep v ix b35)
      { C with block := "land.rhs.i.preheader" }
      (leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35)) 3 := by
  have h35 : evalOperand (contLandS C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandS_35 C s x inc nep ep v ix b35
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hInv rfl h35
  have hres : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
  have hst : s₁ = contP41S C s x inc nep ep v ix b35 := by
    rw [hs₁, hres]; rfl
  rw [hst] at hl₁
  rw [hres] at hl₁
  have h35b : evalOperand (contP41S C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP41S_35 C s x inc nep ep v ix b35
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock39_at (calls := calls) G (ContAC₅ C)
      (contP41S C s x inc nep ep v ix b35) hl₁.inv' rfl h35b
  have hres2 : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
      "LeafBlock35" else "LeafBlock37") = "LeafBlock37" := by rw [hb32]; rfl
  have hst2 : s₂ = contP37S C s x inc nep ep v ix b35 := by
    rw [hs₂, hres2]; rfl
  rw [hst2] at hl₂
  rw [hres2] at hl₂
  have h35c : evalOperand (contP37S C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP37S_35 C s x inc nep ep v ix b35
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock37_at (calls := calls) G { ContAC₅ C with block := "LeafBlock37" }
      (contP37S C s x inc nep ep v ix b35) hl₂.inv' rfl h35c
  have hres3 : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1 then
      "land.rhs.i.preheader" else "if.end372.i") = "land.rhs.i.preheader" :=
    if_pos hbq32
  have hst3 : s₃ = leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35) := by
    rw [hs₃, hres3]; rfl
  rw [hst3] at hl₃
  rw [hres3] at hl₃
  exact ((WalkSegment.of_link hl₁).trans (WalkSegment.of_link hl₂)).trans
    (WalkSegment.of_link hl₃)

/-! ### The total source and stop terms

The run's source and its stop are named as total functions of the bundle's own values, so
the bundle's fields that read the seam state can state it without carrying a state. -/

/-- **The preheader state `%35`'s class selects, as a total function.**  The run's source is
the entry dispatch's target, and the branches on the byte's pivot bits are its three arms;
under the class premise the branch taken *is* the arm's state (`wsPreSAt_33/35/37` at
`contLandS` is this definition's three arms). -/
def wsPreS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
    leafBlock33OutAt (nodeBlock41OutAt (contLandS C s x inc nep ep v ix b35) (cont35 b35))
      (cont35 b35)
  else if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
    leafBlock35OutAt (contP39S C s x inc nep ep v ix b35) (cont35 b35)
  else
    leafBlock37OutAt (contP37S C s x inc nep ep v ix b35) (cont35 b35)

/-- **The stop state the skip reaches from that source**, as a total function of the
bundle's own values.  Under the class premise it is the arm's endpoint, so the fields the
run's endpoint names (`h8c`, `hTail`, the landing) are stated at it. -/
def wsSlS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (k : Nat) : State :=
  wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (wsPreS G C s x inc nep ep v ix b35))
    ix.toNat) ix.toNat v.toNat k

/-! ### The continuing entry's facts, bundled

`HcontCase.ws`'s payload: one argument per head state with an entry left.  This bundle is
the **whitespace** class — the byte before the entry's end is `9`, `10`, `13` or `32` — and
its path is the one the run class's states name: `land.lhs.true357.i`'s target goes through
the three pivots to a leaf, the skip `while.body370.i` runs back over the whitespace, and
`if.end372.i`'s token-end `phi` selects the run's stop `%ee.0.i238`, whose value is `k`.
So the token ends at `k < %cond350.i`, the extra-token scan runs `[k, v.toNat)`, and the
bundle's stopper is `heicd : k < v.toNat`.

**The states are the run class's, and that is the repair.**  The bundle used to be stated at
`contSeamS`/`contEntry`, whose seam stores `%cond350.i = ofNat 64 v.toNat`; `hopS` then
asserted `ei = v.toNat` while `heicd` asserted `ei < v.toNat`, so the bundle was
**uninhabited** wherever a producer could reach it — the same defect `HlastFacts` carried
before its repair, and found by the same instrument (substitute the arm's own values into
every field that names a test, a bound or a span).  At the run class's states
(`contWsSeamS`, `contWsTailStart`, `contWsEntry`, `contWsLatch`, which exist and whose
`%ee.1.i` is `ofNat 64 k` by construction — `contWsEntry_ee`) the two fields agree:
`hopS` follows from the cell, so it is **produced** rather than carried, and `heicd` says
`k < v.toNat`, which is exactly the span the scan visits.  Which class a head state belongs
to is not this bundle's business; the byte before the entry's end decides it, and the
scan-free class is `HcontCleanupFacts`.

**The run, the stop and the price are derived.**  `contWsRunF` takes the class premise
(`hClass`) and `%35`'s dispatch's invariant, and returns the skip's segment from the
whitespace check's target to the seam's entry as the existential count `N`, its bound
`N ≤ 5·(k - ix.toNat) + 10`, and the stop's `%cond350.i` cell — the one cell of the run's
endpoint the invariant does not carry; `contWsPriceAt` derives the price from that count and
the span's two ends.  The class premise is what makes this total: the three arm wrappers
(`contWsRunAt33/35/37`) consume the class's own disjunct, and the segment's source is the
total function `wsPreS` at the class the disjunct selects.  The count is measured rather
than estimated: the entry dispatch at most `4`, the first visit `5` at most (four links at
`LeafBlock43`'s class, five at `46`/`48`'s), the latch visits `≤ 5·(k - i)` (`wsRun`'s own
bound), the seam `1` — so `N ≤ 5·(k - i) + 10`, which is the arm wrappers' statement, and
independent of which leaf stopped the skip.

**What is landed, and what is not.**  The run's *interior* is a theorem: `wsLatchAt` and
`wsStopAt` name the latch at counter `i + n` and the stop at `k`; `wsCont`/`wsStop` are the
byte's three-way class; the leaf states' two cells are `wsLeafS_43/46/48_ee`/`_cond`; and
`wsRun` is the induction — from the latch at `i` to `wsStopAt … k`, at the target carry
`{ C with block := "if.end372.i" }`, carrying the target's invariant, both cells, and the
existential bound `∃ n, n ≤ 5·(k - i) ∧ WalkSegment … n`.  The statement is the *strengthened*
one purpose: a step's input is the previous step's output, and a segment's `inv'` does not
name `%ee.0.i238` or `%cond350.i`, so segment, invariant and cells travel together.  Landed
beside it is the composition around it — the entry dispatch from `contLandS` to the
preheader, which is `%35`'s class (`wsEntry33/35/37`: `NodeBlock41 → LeafBlock33 → preheader`
in two links, `NodeBlock41 → NodeBlock39 → LeafBlock35/37 → preheader` in three), the first
visit at `%idxprom.i`'s own byte `i` (`wsFirstSeg43/46/48`; `wsRun` starts at the latch, whose
first read is `i + 1`), the seam (`wsSeamSeg`), the price (`wsPrice`), and their join
(`contWsAfterPreAt`, `contWsRunAt33/35/37`).

Its price `N + 8·(v - 1 - k) ≤ 8·ΔA + 5` absorbs the count (`wsPrice`, `contWsPriceAt`),
because `8(v - 1 - i) ≤ 8·ΔA - 8` from `hspan` and `entryPos C.k ≤ i`, so the left side is
at most `8·ΔA - 3·(k - i) + 2`.  The two premises that price and the traversal need beside
the count are `hClass`'s last two conjuncts: `entryPos C.k ≤ ix.toNat` for the run's start
(`hstart` is about the *stop* `k`), and `v.toNat - ix.toNat ≤ C.inner`, the entry's inner
budget, which no clause of `WalkInv` fixes at the run's start and which the first visit's
`ScanEntered` and the exit's `ScanCount` consume.  The per-index class `∀` reaches
`ix.toNat` itself, because the first visit reads the entry's own first byte.

**The class is a field, and the run is not.**  `HcontFacts` is a `Type` produced at every
head state with an entry left, while the run's derivation is conditional on `%35`'s class:
the three arm wrappers take that class as a disjunction.  A `def` cannot inhabit the bundle
at a class that does not enter the skip without that premise, so the class enters as
`hClass` and the run leaves the bundle.  The count follows: the committed bundle is 64
fields; this one retires `sl`, `b8`, `hRun`, `hnRun`, `hcond_sl` and the count `n`, and adds
`hClass` — 64 − 6 + 1 = 59.  `b8` is `x1` (the seam's byte, which the retired `hRun` pinned
to the run's endpoint), `sl` is the term `wsSlS`, `hcond_sl` is `contWsRunF`'s third
conjunct, `hRun` and `hnRun` are `contWsRunF` and `contWsPriceAt`, and `n` is the count
`contWsRunF` returns existentially and no field reads.

Two steps spare against the entry allowance, which the price below spends.

Three witnesses are *consequences* rather than free data, and the bundle writes the
consequence instead of a witness plus an equation:

* the landing's index — the scan's entry `phi` selects `%ee.1.i`, whose cell the seam fixed
  at `ofNat 64 k`, so the index is `k` and `latch_counter` reads the latch's cell there;
* the scan's bound — `%cond350.i` is `cond.end349.i`'s own cell and no block from there to
  the latch rebinds it, so the bundle carries the lane's word `v` and writes `v.toNat`
  wherever the bound appears; `contLatch_cond` is the peel that says the latch's cell is
  `ofNat 64 v.toNat`;
* the `phi`'s selection at `cond.end349.i` — the predecessor is `cond.true345.i`, so the
  selection is `%conv347.i` by a closed `phi` computation (`contPhi6`), and the cell it
  selects is the link's own (`cte345OutAt_conv`).

**One cell at the run's endpoint is derived and two are the invariant's.**  `%inc.i` and
`%nep` are `WalkInv`'s own — `inc_reg` and one of `walkStaticRegs`' rows — and the seam binds
neither, so the segment's target invariant reads them at the endpoint (`contWsSeamS_inc`,
`contWsSeamS_nep`).  `%cond350.i` is not a clause of the invariant: it is bound once at
`cond.end349.i` and no block of the skip rebinds it, and a `WalkSegment` records a run and its
target's invariant rather than the blocks the run passed — so the run's producer returns the
cell as its third conjunct (`contWsRunF`), carried through the arms' latch induction beside
the segment, and no field states it. -/
structure HcontFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0
  hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0
  hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0
  /-- The entry's index and the stream's count, and the count test's value.  `hnext` is
  `1` — a continuing entry has one after it — and it is the field that used to be `hge`
  with `= 0`: see this module's header for the arithmetic that made that uninhabited. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- **The next entry's position lane**: the table's pointer, the load's word, and the
  read.  `cond.true345.i` is three instructions — `gep`, `load i32`, `zext` — and this is
  what its step consumes. -/
  ep : Nat
  v : BitVec 32
  h5 : lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (contAS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The default arm's remaining cells, at the state `cond.true345.i` leaves. -/
  ix : BitVec 64
  hidx5 : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (contAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  /-- **The entry is not empty.**  `%cond350.i` is the next entry's position, above this
  entry's own index, so `cond.end349.i` takes `land.lhs.true357.i`.

  **Arm-specific:** the last entry's bundle carries the opposite value, because its
  `%cond350.i` is `%4` and the last entry ends the stream.  Two bundles can share a field
  name and correctly carry opposite values. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The byte before the entry's end**, which the whitespace check reads: its address is
  `%cond350.i - 1` and the document supplies the byte.  Its class is `hClass`'s first
  conjunct, stated on `cont35 b35`. -/
  b35 : UInt8
  hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  /-- **The whitespace skip's stop, its byte and its document group.**  `k` is the run's
  stop (which the token-end `phi` selects) and `x1` the head's byte at the seam.

  `hClass` is **the one supplied field that makes the run's segment total at this state**:
  `%35` is one of the four whitespace bytes, so the leaf the three pivots reach takes its
  *true* arm and the walk enters the skip; every byte the skip reads continues the token
  until `k`, which stops it.  Without it a total producer could not build the segment at
  the other classes — this bundle would be inhabited only by the whitespace arm.  The run
  itself is not a field: `contWsRunF` derives it from this class and the composition
  (`contWsRunAt33/35/37`), at a count of at most `5·(k - ix.toNat) + 10`, with the stop's
  `%cond350.i` cell beside it, and `contWsPriceAt` derives the price from that count and the
  span's two ends.

  The group is stated in the bundle's own vocabulary: the class bits are on `cont35 b35`;
  the skip's are on `wsX G` at the index the latch carries (`ix.toNat`), and they reach
  `ix.toNat` itself because the first visit reads the entry's own first byte; `k` is the
  stop.  The group's last conjuncts are the inner budget the first visit's `ScanEntered`
  witness needs and the `entryPos` fact the price's `+5` rests on. -/
  k : Nat
  x1 : BitVec 8
  hClass :
    ((evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)) ∧
    (∀ q, ix.toNat ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧ ix.toNat < k ∧
    v.toNat - ix.toNat ≤ C.inner ∧ entryPos G C.k ≤ ix.toNat
  /-- The run's stop is inside the entry, which is what makes the extra-token span
  `[k, v.toNat)` non-empty.  **This is the field the other class cannot carry**: on the
  scan-free arm the token's end is the entry's end, so `k` would be `v.toNat`. -/
  heicd : k < v.toNat
  /-- The entry's first byte's class, read at the seam's name. -/
  h8c : evalOperand (contWsSeamS C (wsSlS G C s x inc nep ep v ix b35 k) k x1)
    (.reg "%8") = some (.int 8 x1)
  hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0
  /-- The tail's own: its three call outcomes, the event it emits, the seed's words and
  its segment from the class-C span's target to `contWsEntry` — `consumerTailSegAt` at
  count `3`, its first index the run's stop `k` and its bound the lane's word.  The scan's
  entry `phi` is `%ee.1.i` on `if.then447.i`'s edge, and the seam fixed that cell at
  `ofNat 64 k` (`contWsEntry_ee`), which is why `hopS` is a theorem here and not a field. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
    (contWsTailStart C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1)
    (TailCarryScan (ContTailStartC C) ev)
    (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA) 3
  /-- The scan's landing: the byte's address and the byte.  The index is `k` — the seam's
  stored end — everywhere the landing's states name it. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
    cA rdv xA).env "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
    (landRhs457OutAt (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
      cA rdv xA) (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v
      cA rdv xA) (BitVec.ofNat 64 k) a q)
    (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
    (ScanS₉₆ (contWsEntry C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (contWsLatch C (wsSlS G C s x inc nep ep v ix b35 k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA
      (BitVec.ofNat 64 k) a q x47)
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and the run's stop at or after this one's — the two facts that make
  the visits and the run no more than the span, and the price's byte term. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ k
  /-- **The traversal's round**, produced: `scanRoundField` at the lane's bound, so no
  premise supplies it.  A visit at the byte the landing loads, at the counter's own index
  and the lane's bound. -/
  hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
    (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    p + 1 < v.toNat → p + 1 < 2 ^ 63 →
    lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i").env
      "%3" = some (.ptr a) →
    readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
    evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
      "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
    evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
    evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
    WalkLocal (ScanC₁₀₅ (ScanCLand C'))
      (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) →
    WalkLocal (ScanC₉₆ (ScanCLand C'))
      (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    WalkLocal { ScanCLand C' with block := "while.body462.i" }
      (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
      WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
    C'.block = "while.body462.i" → k < p + 1 → p + 1 < v.toNat →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i").env "%3" = some (.ptr a) ∧
      readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) ∧
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x)
  /-- **The token record's register at the scan's exit.**  Stated over the states the
  traversal's counters pin, because `walkScanRounds457_of_cell` returns its final state
  existentially; every block on the path binds its own cells and none rebinds `%t352.i`,
  so the fact is true of the model and the shape is the traversal's.

  **Derived, not supplied.**  The register is one of `walkStaticRegs`, so `WalkInv.regs`
  carries it at every state the field quantifies over — the field's `∀` is over the
  invariant's states, not over the traversal's existential endpoint — and the producer
  fills it with a term, not with an argument: `scanTokField` (a `∀` in one line) or its
  twin `cont_static_tok`. -/
  htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok)

/-! ### The seam's byte test

`%8`'s test at the seam is clear when the byte is at or above `110`: the `45` branch and
the `[48, 58)` window are both below it.  `slt` on bytes is signed, and the hypothesis rules
out the `[128, 256)` half, so the byte is in `[110, 128)` — below `256`, and its `+ 208`
wraps to `x - 48`, which is at least `62`. -/
theorem wsBit45 {x : BitVec 8}
    (h : evalICmp .slt x (BitVec.ofNat 8 110) = 0) :
    (evalICmp .eq x (BitVec.ofNat 8 45) ||| evalICmp .ult (x + BitVec.ofNat 8 208)
      (BitVec.ofNat 8 10)) = 0 := by
  -- the signed test is the byte's `toInt`, so the byte is at or above `110`
  have hslt : ¬ (x.toInt < ((BitVec.ofNat 8 110) : BitVec 8).toInt) := by
    rw [show evalICmp .slt x (BitVec.ofNat 8 110) =
      BitVec.ofBool (decide (x.toInt < (BitVec.ofNat 8 110).toInt)) from rfl] at h
    cases hd : decide (x.toInt < (BitVec.ofNat 8 110).toInt) with
    | false => exact of_decide_eq_false hd
    | true => rw [hd] at h; exact absurd h (by decide)
  have h110 : ((BitVec.ofNat 8 110) : BitVec 8).toInt = (110 : Int) := by decide
  rw [h110] at hslt
  have hx110 : 110 ≤ x.toNat := by
    unfold BitVec.toInt at hslt
    split at hslt <;> omega
  have hx256 : x.toNat < 256 := x.isLt
  -- `45` is one of the bytes below `110`
  have heq : evalICmp .eq x (BitVec.ofNat 8 45) = 0 := by
    rw [show evalICmp .eq x (BitVec.ofNat 8 45) =
      BitVec.ofBool (decide (x = BitVec.ofNat 8 45)) from rfl]
    have h45 : ((BitVec.ofNat 8 45) : BitVec 8).toNat = 45 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 45 < 2 ^ 8)]
    have hne : x ≠ BitVec.ofNat 8 45 := by
      intro he
      rw [he, h45] at hx110
      omega
    rw [decide_eq_false hne]
    rfl
  -- `x + 208` wraps to `x - 48`, which is at least `62`
  have hult : evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) = 0 := by
    rw [show evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) =
      BitVec.ofBool ((x + BitVec.ofNat 8 208).ult (BitVec.ofNat 8 10)) from rfl]
    have h208 : ((BitVec.ofNat 8 208) : BitVec 8).toNat = 208 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 208 < 2 ^ 8)]
    have hsum : (x + BitVec.ofNat 8 208).toNat = x.toNat - 48 := by
      rw [BitVec.toNat_add, h208]
      have hrew : x.toNat + 208 = (x.toNat - 48) + 256 * 1 := by omega
      rw [hrew, show (2 : Nat) ^ 8 = 256 from rfl, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    have h10 : ((BitVec.ofNat 8 10) : BitVec 8).toNat = 10 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 10 < 2 ^ 8)]
    have hnlt : ¬ (x + BitVec.ofNat 8 208).ult (BitVec.ofNat 8 10) := by
      rw [BitVec.ult_iff_toNat_lt, hsum, h10]
      omega
    cases hb : (x + BitVec.ofNat 8 208).ult (BitVec.ofNat 8 10) with
    | false => rfl
    | true => exact absurd hb hnlt
  rw [heq, hult]
  decide

/-- The skip rebinds no static register: every state it passes is the previous state's
environment with its own cells in front, and `%end.i` is none of them.  The seam's step
stores that cell, so the run's producer reads it off the head state's invariant
(`WalkInv.regs`). -/
theorem scanLatchOut_envEnd (s : State) (i c : Nat) (t : String) :
    lookupName (scanLatchOut s "%inc371.i" "%exitcond.not" i c t).env "%end.i" =
      lookupName s.env "%end.i" := by
  simp only [stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `wsLeafS` at either class keeps the static register: its three arms bind the pivots,
the switch leaf and the landing's three cells, none of which is `%end.i`. -/
theorem wsLeafS_envEnd {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    lookupName (wsLeafS G s p).env "%end.i" = lookupName s.env "%end.i" := by
  simp only [wsLeafS]
  split
  · simp only [leafBlock43OutAt, nodeBlock52OutAt, wsLandS, landRhsIOutAt, stateAt, cells,
      State.bind, State.bindAll]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [scanNodeBlock50In, wsLandS, landRhsIOutAt, stateAt, cells, State.bind,
        State.bindAll]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [scanNodeBlock50In, wsLandS, landRhsIOutAt, stateAt, cells, State.bind,
        State.bindAll]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The latch at `n` visits keeps the static register. -/
theorem wsLatchAt_envEnd {m0 : Mem} (G : WalkGeom m0) (l : State) (i v : Nat) :
    ∀ n, lookupName (wsLatchAt G l i v n).env "%end.i" = lookupName l.env "%end.i"
  | 0 => rfl
  | n + 1 => by
    simp only [wsLatchAt]
    rw [wsLeafS_envEnd, scanLatchOut_envEnd, wsLatchAt_envEnd G l i v n]

/-- The stop state keeps the static register, whichever leaf stopped the skip. -/
theorem wsStopAt_envEnd {m0 : Mem} (G : WalkGeom m0) (l : State) (i v k : Nat) :
    lookupName (wsStopAt G l i v k).env "%end.i" = lookupName l.env "%end.i" := by
  unfold wsStopAt
  split
  · rfl
  · simp only [wsStopS]
    rw [wsLeafS_envEnd, scanLatchOut_envEnd, wsLatchAt_envEnd]

/-- The entry dispatch keeps the static register: its four nodes and three leaves bind
the pivots and the lane's cells, and `contLandS`'s two are the byte's. -/
theorem wsPreS_envEnd {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (wsPreS G C s x inc nep ep v ix b35).env "%end.i" =
      lookupName (contLandS C s x inc nep ep v ix b35).env "%end.i" := by
  simp only [wsPreS]
  split
  · simp only [leafBlock33OutAt, nodeBlock41OutAt, contLandS, contEndS, condEnd349OutAt,
      cte345OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [leafBlock35OutAt, contP39S, contP41S, contLandS, contEndS,
        condEnd349OutAt, cte345OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt,
        cells, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [leafBlock37OutAt, contP37S, contP41S, contLandS, contEndS,
        condEnd349OutAt, cte345OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt,
        cells, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **The run's endpoint keeps `%end.i`**, so the seam's stored end is the head state's
cell. -/
theorem wsSlS_envEnd {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (k : Nat) :
    lookupName (wsSlS G C s x inc nep ep v ix b35 k).env "%end.i" =
      lookupName (contLandS C s x inc nep ep v ix b35).env "%end.i" := by
  simp only [wsSlS, landRhsPreheaderOutAt]
  rw [wsStopAt_envEnd, wsLeafS_envEnd, wsPreS_envEnd]

/-! #### `%cond350.i` through the skip

The copy call's bound is the lane's word, and every state the skip passes keeps it: the
pivots, the switch leaf and the landing's three cells are the states' own binds, and none
of them is `%cond350.i`.  The `%end.i` family above has the same shape; this one is needed
because the run's tail states its copy call at the byte's leaf, so the bound has to be read
there rather than at the check state.  The three-way byte split and `wsStopAt`'s
`match k - i` are why the peel cannot be one `simp`: each arm's binds are its own. -/

/-- The latch's step keeps `%cond350.i`. -/
theorem scanLatchOut_cond (s : State) (i c : Nat) (t : String) :
    lookupName (scanLatchOut s "%inc371.i" "%exitcond.not" i c t).env "%cond350.i" =
      lookupName s.env "%cond350.i" := by
  simp only [stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The leaf keeps it, whichever of the three arms stopped the skip. -/
theorem wsLeafS_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    lookupName (wsLeafS G s p).env "%cond350.i" = lookupName s.env "%cond350.i" := by
  simp only [wsLeafS]
  split
  · simp only [leafBlock43OutAt, nodeBlock52OutAt, wsLandS, landRhsIOutAt, stateAt, cells,
      State.bind, State.bindAll]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [scanNodeBlock50In, wsLandS, landRhsIOutAt, stateAt, cells, State.bind,
        State.bindAll]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [scanNodeBlock50In, wsLandS, landRhsIOutAt, stateAt, cells, State.bind,
        State.bindAll]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The latch at `n` visits keeps it. -/
theorem wsLatchAt_cond {m0 : Mem} (G : WalkGeom m0) (l : State) (i v : Nat) :
    ∀ n, lookupName (wsLatchAt G l i v n).env "%cond350.i" = lookupName l.env "%cond350.i"
  | 0 => rfl
  | n + 1 => by
    simp only [wsLatchAt]
    rw [wsLeafS_cond, scanLatchOut_cond, wsLatchAt_cond G l i v n]

/-- The stop's leaf, at `if.end372.i`, keeps it: the arm binds cells and moves the edge,
nothing else. -/
theorem wsStopS_cond {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    lookupName (wsStopS G s p).env "%cond350.i" = lookupName s.env "%cond350.i" := by
  simp only [wsStopS]
  exact wsLeafS_cond G s p

/-- The stop state keeps it, whichever leaf stopped the skip. -/
theorem wsStopAt_cond {m0 : Mem} (G : WalkGeom m0) (l : State) (i v k : Nat) :
    lookupName (wsStopAt G l i v k).env "%cond350.i" = lookupName l.env "%cond350.i" := by
  unfold wsStopAt
  split
  · rfl
  · simp only [wsStopS]
    rw [wsLeafS_cond, scanLatchOut_cond]
    exact wsLatchAt_cond G l i v _

/-- The scan's entry, at the bundle's own terms.  Named for the same reason
`hlastEntryF` is: the bundle's fields are the `def`s' arguments in order, so a lemma's
statement at `contWsEntryF f` is the one its field types spell out. -/
abbrev contWsEntryF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  contWsEntry C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1 f.x1
    f.r₁ f.r₂ f.r₃ f.k f.v f.cA f.rdv f.xA

/-- The scan's latch, at the bundle's own terms. -/
abbrev contWsLatchF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  contWsLatch C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1 f.x1
    f.r₁ f.r₂ f.r₃ f.k f.v f.cA f.rdv f.xA (BitVec.ofNat 64 f.k) f.a f.q f.x47

/-! ### The no-run class's bundle

`HcontFacts` describes the token that ends *inside* its entry, so the extra-token scan runs
over `[ei, v.toNat)` and the walk enters it.  A continuing entry whose token ends at the
entry's end is the other class: `%ee.1.i` *is* `%cond350.i`, `if.then447.i`'s target tests
`ult v v`, and the walk reaches `if.end473.i` — the merge's entry — without a scan.  That is
`HcontCleanupFacts`, the sibling this module's header plans, and it is a bundle of its own
rather than a mode of `HcontFacts`: the fields it does not have are the reason.

**What the split removes.**  No scan index (`ei`), no stopper (`heicd`), no landing group
(`a`, `q`, `bs`, `src`, `sel`, `hpreS`, `hincS`, `hopS`, `h3S`, `hpos`, `hreadS`, `hbsS`,
`hloc105`, `x47`, `h47`, `hbit47`, `hws47`, `hloc96`, `hlatch`), no span (`hspan`,
`hstart`), no traversal (`hround`, `hguard`, `hbyte`) and no token register across the scan
(`htok`).  What it keeps is the class's chain to the tail's start (`hcontToSpan`'s inputs),
the tail's three calls on their empty arm, and the byte before the entry's end.

**Why the byte is carried as a route and not as three bits.**  The bundle's fields are read
at the byte's pivots, and the pivots' target depends on the byte's class: the scan-free
class takes `NodeBlock41 → NodeBlock39 → LeafBlock35`, the low leaf
`NodeBlock41 → LeafBlock33`, the high leaf `NodeBlock41 → NodeBlock39 → LeafBlock37`.  A
bundle stated at `contP35S` — the scan-free endpoint — can only describe a document whose
byte is that class.  `HcontByteRoute` is the class, `contPByte`-free: the cell fields are
stated at the `NodeBlock41` state every route leaves them at, and the seam is
`contSeamByte`, whose cells are the same at all three endpoints.

**Why the price has no byte term.**  The bundle's segment is the class's chain
(`hcontPrefixCleanupSeg`: the head's eight links, the byte's three or four and the class-C
span's five) plus the merge's one; nothing in it consumes a document byte beyond the two
the whitespace check reads, so the entry allowance pays it whole: `p + 2 ≤ 32·Δk` at
`p ≤ 21` and `Δk = 1`.  The whitespace class is the one whose price needs `8·ΔA` — its
scan's visits — and that is the arm `HcontFacts` describes. -/
structure HcontCleanupFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The head's byte and its four pivot bits. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0
  hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0
  hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0
  /-- The counts and the count test's value: `1`, a continuing entry has one after it. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- The next entry's position lane: the table's pointer, the load's word and the read. -/
  ep : Nat
  v : BitVec 32
  h5 : lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (contAS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The default arm's remaining cells. -/
  ix : BitVec 64
  hidx5 : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (contAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  /-- The entry is not empty, so the whitespace check reads the byte before its end. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The byte before the entry's end and its class.**  The three pivots take the class's
  leaf to `if.end372.i`; the route is what makes the seam's stored end the entry's own end
  at every leaf, and what lets the class's chain be composed rather than assumed. -/
  b35 : UInt8
  hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  hb : HcontByteRoute (cont35 b35)
  /-- The seam's cells: the stored end at `%end.i`, the byte and its two literal tests,
  read at the `NodeBlock41` state the class's pivots leave them at. -/
  b8 : BitVec 8
  hend : lookupName (contLandS C s x inc nep ep v ix b35).env "%end.i" =
    some (.ptr (C.stage.tok + 8))
  h8end : lookupName (contLandS C s x inc nep ep v ix b35).env "%8" = some (.int 8 b8)
  hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
    evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The entry's first byte's class, read at the class's own seam. -/
  x1 : BitVec 8
  h8c : evalOperand (contSeamByte (contLandS C s x inc nep ep v ix b35) v.toNat
    C.stage.tok b35 b8 hb) (.reg "%8") = some (.int 8 x1)
  hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0
  /-- The tail's three calls, its event and the seed's words: its segment on the empty arm,
  reaching `if.end473.i` with `TailCarryEnd`'s carry, from the class's own seam. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
    (contTailStartByte C s x inc nep ep v ix b35 b8 x1 hb)
    (TailCarryEnd (ContTailStartC C) ev)
    (contCleanupEndByte C s x inc nep ep v ix b35 b8 x1 hb r₁ r₂ r₃ cA rdv xA) 3

/-- The class's tail end, at the bundle's own terms. -/
abbrev contCleanupEndF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  contCleanupEndByte C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.hb f.r₁ f.r₂
    f.r₃ f.cA f.rdv f.xA

/-- The tail's start, at the bundle's own terms: the segment's source, where the body of
the merge's composition reads its cells. -/
abbrev contTailStartF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  contTailStartByte C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.hb

/-- **The scan's visits, counted with the registers kept.**  `walkScanRounds457_of_cell` counts
the visits but keeps only the counter at its target; the exit test reads the bound too, so
the recursion here is at the round's own granularity (`hround`, the traversal's own
hypothesis) and its conclusion carries both registers.  The price bound is the traversal's
own: one byte allowance per visit, `cd - 1 - ei` of them.

**This is the two-register twin of `walkScanRounds457_of_cell`, not a simplification of it, and it
must not be folded back into that lemma.**  The committed traversal concludes
`%q.0.i246 = c - 1` and nothing about `%cond350.i`, while the latch's exit test branches on
the bound (`i + 1 = c`) — so the exit is unreachable from its conclusion by construction,
whatever the induction does inside.  The extra register is not a strengthening for its own
sake: it is what the exit consumes, and the price bound is unchanged. -/
theorem contScanRounds {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s) {C' : WalkCarry G} {s' : State} {i : Nat}
    (hInv : WalkInv G C' s') (hblock : C'.block = "while.body462.i")
    (hi : lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hb : lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)))
    (hc63 : f.v.toNat ≤ 2 ^ 63) (hic : i < f.v.toNat) (hik : f.k ≤ i) :
    ∃ (C'' : WalkCarry G) (s'' : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' n ∧ WalkInv G C'' s'' ∧
      C''.block = "while.body462.i" ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
      n ≤ stage2ByteAllowance * (f.v.toNat - 1 - i) := by
  have go : ∀ r, ∀ (j : Nat) (K : WalkCarry G) (t : State), f.v.toNat - 1 - j = r →
      WalkInv G K t → K.block = "while.body462.i" →
      lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 j)) →
      lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) →
      j < f.v.toNat → f.k ≤ j →
      ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
        K'.block = "while.body462.i" ∧
        lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
        lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
        n ≤ stage2ByteAllowance * r := by
    intro r
    induction r with
    | zero =>
        intro j K t _ hInv hblock hi hb hic _
        have hie : j = f.v.toNat - 1 := by omega
        exact ⟨K, t, 0, Seg.measure (Seg.nil hInv), hInv, hblock,
          by rw [← hie]; exact hi, hb, by simp⟩
    | succ r ih =>
        intro j K t hr hInv hblock hi hb hic hlo
        have hlt : j + 1 < f.v.toNat := by omega
        have hpos : j + 1 < 2 ^ 63 := by omega
        obtain ⟨a, bs, q, x, h3, hread, hbs, h47, hbit, hws, hl105, hl96, hll⟩ :=
          f.hbyte K t j hInv hblock (by omega) hlt hi hb
        obtain ⟨K₁, t₁, j₁, hseg, hInv₁, hb₁, hj, hi₁, hc₁⟩ :=
          f.hround K t j a bs q x hInv hblock hi hb hlt hpos h3 hread hbs h47 hbit hws
            hl105 hl96 hll
        obtain ⟨K₂, t₂, m, hseg₂, hInv₂, hb₂, hi₂, hc₂, hm⟩ :=
          ih (j + 1) K₁ t₁ (by omega) hInv₁ hb₁ hi₁ hc₁
            (by omega) (by omega)
        refine ⟨K₂, t₂, j₁ + m, hseg.trans hseg₂, hInv₂, hb₂, hi₂, hc₂, ?_⟩
        rw [Nat.mul_succ]
        omega
  exact go (f.v.toNat - 1 - i) i C' s' rfl hInv hblock hi hb hic hik

/-! ### The two arms' compositions, and where they are

Neither arm's composition lives here.  The whitespace arm's goes through the run
(`contWsRunF`), the seam, the class-C span, the tail and the scan's visits, and it
records the merge's three cells; the scan-free arm's is `hcontPrefixCleanupSeg` plus the
merge's step.  Both are `JsonStage2WalkRevolutionSeg`'s (`walkRevolutionMergeSegWs` and
`walkRevolutionMergeSeg`), because the cells are read at the endpoint's named state and the
traversal that carries the registers is that module's.

The composition this file used to state (`walkRevolution_seg`) is gone rather than kept
beside them: its premise was the bundle at the *scan-free* states, so it named a path the
walk does not take from a state the walk does reach — the vacuity this module's header
records.  What survives here is the bundle, and the traversal lemma (`contScanRounds`) both
arms' compositions share. -/

/-! ### The run's composition around `wsRun`

The pieces above with `wsRun`: the entry dispatch by `%35`'s class (`wsEntry33/35/37`), the
first visit at the entry's own byte (`wsFirstSeg43/46/48`), the run (`wsRun`), and the seam
(`wsSeamSeg`).  `contWsAfterPre` is the uniform tail from the preheader; the three arms
apply their dispatch and hand it the preheader.  The count is `5·(k - i) + 10`: the entry is
at most four links, the first visit five, the run five a byte, and the seam one. -/

/-! ### The stop state's predecessor, at each stop class

`wsStopAt` unfolds by `match k - i`, and `hik : i < k` makes the successor arm the one
taken; `wsStopS` is `wsLeafS` with the block moved, so its `pre` is the leaf's — one name
per stop class. -/

/-- The stop state's predecessor at `LeafBlock43`'s class. -/
theorem wsStopAt_pre43 {m0 : Mem} (G : WalkGeom m0) (l : State) {i v k : Nat}
    (hik : i < k) (hstop13 : evalICmp .slt (wsX G k) (BitVec.ofNat 8 13) = 1) :
    (wsStopAt G l i v k).pre = some "LeafBlock43" := by
  have hki : k - i = (k - i - 1) + 1 := by omega
  have hp : i + (k - i - 1) + 1 = k := by omega
  rw [wsStopAt, hki]
  show (wsStopS G (scanLatchOut (wsLatchAt G l i v (k - i - 1)) "%inc371.i"
    "%exitcond.not" (i + (k - i - 1)) v "land.rhs.i") (i + (k - i - 1) + 1)).pre =
    some "LeafBlock43"
  rw [hp, wsStopS, wsLeafS_43 G _ k hstop13]
  rfl

/-- The stop state's predecessor at `LeafBlock46`'s class. -/
theorem wsStopAt_pre46 {m0 : Mem} (G : WalkGeom m0) (l : State) {i v k : Nat}
    (hik : i < k) (hstop13 : evalICmp .slt (wsX G k) (BitVec.ofNat 8 13) = 0)
    (hstop32 : evalICmp .slt (wsX G k) (BitVec.ofNat 8 32) = 1) :
    (wsStopAt G l i v k).pre = some "LeafBlock46" := by
  have hki : k - i = (k - i - 1) + 1 := by omega
  have hp : i + (k - i - 1) + 1 = k := by omega
  rw [wsStopAt, hki]
  show (wsStopS G (scanLatchOut (wsLatchAt G l i v (k - i - 1)) "%inc371.i"
    "%exitcond.not" (i + (k - i - 1)) v "land.rhs.i") (i + (k - i - 1) + 1)).pre =
    some "LeafBlock46"
  rw [hp, wsStopS, wsLeafS_46 G _ k hstop13 hstop32]

/-- The stop state's predecessor at `LeafBlock48`'s class. -/
theorem wsStopAt_pre48 {m0 : Mem} (G : WalkGeom m0) (l : State) {i v k : Nat}
    (hik : i < k) (hstop13 : evalICmp .slt (wsX G k) (BitVec.ofNat 8 13) = 0)
    (hstop32 : evalICmp .slt (wsX G k) (BitVec.ofNat 8 32) = 0) :
    (wsStopAt G l i v k).pre = some "LeafBlock48" := by
  have hki : k - i = (k - i - 1) + 1 := by omega
  have hp : i + (k - i - 1) + 1 = k := by omega
  rw [wsStopAt, hki]
  show (wsStopS G (scanLatchOut (wsLatchAt G l i v (k - i - 1)) "%inc371.i"
    "%exitcond.not" (i + (k - i - 1)) v "land.rhs.i") (i + (k - i - 1) + 1)).pre =
    some "LeafBlock48"
  rw [hp, wsStopS, wsLeafS_48 G _ k hstop13 hstop32]

/-! ### The composition from the preheader

The entry dispatch has already been applied by the caller (the arm fixes `pre`), so this
theorem is the uniform tail: the first visit at the entry's own byte, `wsRun` from the latch
it reaches, the seam at the stop, and the count. -/

/-- **The run's tail from the preheader, at any check state.**  The first visit at the
entry's own byte `i` (one visit outside `wsRun`, whose first read is `i + 1`), the run from
the latch to the stop `k`, and the seam — with the stop's `%cond350.i` cell as the third
conjunct, which is the one run-endpoint cell the invariant does not carry.  The entry
dispatch is the caller's (`wsEntryAt33/35/37`), so the source is the state parameter. -/
theorem contWsAfterPreAt {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (v : BitVec 32) (ix : BitVec 64) (pre : State) {k : Nat} {b8 : BitVec 8}
    {j : Nat}
    (hEntry : WalkSegment calls G (ContAC₄ C) sl
      { C with block := "land.rhs.i.preheader" } pre j)
    (hj : j ≤ 4)
    (hpc : pre.pc = "land.rhs.i.preheader")
    (hidx : lookupName pre.env "%idxprom.i" = some (.int 64 ix))
    (hcond : lookupName pre.env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
      ix.toNat v.toNat k).env "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
      ix.toNat v.toNat k).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl (ContSeamC C)
        (contWsSeamS C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k) k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
        ix.toNat v.toNat k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  -- the preheader's entry fact and the first visit's landing fact
  have hie : (BitVec.ofNat 64 ix.toNat) = ix := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hscan : ScanEntered { pre with pc := "land.rhs.i", pre := some pre.pc }
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner := by
    refine ⟨ix.toNat, v.toNat, hvsub, hiv, hcw, ?_, ?_, ?_⟩
    · show some pre.pc = some "land.rhs.i.preheader"
      rw [hpc]
    · show lookupName pre.env "%idxprom.i" = some (.int 64 (BitVec.ofNat 64 ix.toNat))
      simpa only [hie] using hidx
    · exact hcond
  have hsc2 : ScanCount (landRhsIOutAt G (landRhsPreheaderOutAt pre)
      (BitVec.ofNat 64 ix.toNat) (scanB G (BitVec.ofNat 64 ix.toNat)))
      "%ee.0.i238" "%cond350.i" C.inner := by
    rw [scanB_ofNat G hi63]
    refine ⟨ix.toNat, v.toNat, hvsub, hiv, hcw, ?_, ?_⟩
    · simpa only [wsLandS] using wsLandS_ee G (landRhsPreheaderOutAt pre) ix.toNat
    · simpa only [wsLandS] using
        wsLandS_cond G (landRhsPreheaderOutAt pre) ix.toNat hcond
  -- the first visit, by the entry's own byte's class
  have hFirst : ∃ first, first ≤ 5 ∧
      WalkSegment calls G { C with block := "land.rhs.i.preheader" } pre
        { C with block := "while.body370.i" }
        (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat) first := by
    rcases hcontI with ⟨h13, hws0⟩ | ⟨h13, h32, hq13⟩ | ⟨h13, h32, hq32⟩
    · exact ⟨4, by omega, wsFirstSeg43 G C pre hEntry.inv' hpc hscan
        (by simpa only [evalOperand, landRhsPreheaderOutAt, hie] using hidx)
        rfl hi63 hgn halen hevlen h13 hws0 hsc2⟩
    · exact ⟨5, by omega, wsFirstSeg46 G C pre hEntry.inv' hpc hscan
        (by simpa only [evalOperand, landRhsPreheaderOutAt, hie] using hidx)
        rfl hi63 hgn halen hevlen h13 h32 hq13 hsc2⟩
    · exact ⟨5, by omega, wsFirstSeg48 G C pre hEntry.inv' hpc hscan
        (by simpa only [evalOperand, landRhsPreheaderOutAt, hie] using hidx)
        rfl hi63 hgn halen hevlen h13 h32 hq32 hsc2⟩
  obtain ⟨first, hfirst, hsegFirst⟩ := hFirst
  -- the run from the latch the first visit reaches
  have hiLatch : lookupName (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat).env
      "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 ix.toNat)) := by
    rcases hcontI with ⟨h13, -⟩ | ⟨h13, h32, -⟩ | ⟨h13, h32, -⟩
    · exact wsLeafS_43_ee G (landRhsPreheaderOutAt pre) ix.toNat h13
    · exact wsLeafS_46_ee G (landRhsPreheaderOutAt pre) ix.toNat h13 h32
    · exact wsLeafS_48_ee G (landRhsPreheaderOutAt pre) ix.toNat h13 h32
  have hcLatch : lookupName (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rcases hcontI with ⟨h13, -⟩ | ⟨h13, h32, -⟩ | ⟨h13, h32, -⟩
    · exact wsLeafS_43_cond G (landRhsPreheaderOutAt pre) ix.toNat v.toNat h13 hcond
    · exact wsLeafS_46_cond G (landRhsPreheaderOutAt pre) ix.toNat v.toNat h13 h32 hcond
    · exact wsLeafS_48_cond G (landRhsPreheaderOutAt pre) ix.toNat v.toNat h13 h32 hcond
  obtain ⟨n, hn, hsegRun, -, heeSl, hcondSl⟩ :=
    wsRun (calls := calls) G { C with block := "while.body370.i" }
      (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
      hsegFirst.inv' rfl hiLatch hcLatch hcw hik hkv hcls hstop hpos hqn halen hevlen
  -- the seam at the stop's class
  have hSeam : ∃ seam, seam ≤ 1 ∧
      WalkSegment calls G { C with block := "if.end372.i" }
        (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat) ix.toNat v.toNat k)
        (ContSeamC C)
        (contWsSeamS C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k) k b8) seam := by
    rcases hstop with ⟨h13, hws⟩ | ⟨h13, h32, hq⟩ | ⟨h13, h32, hq⟩
    · have hpre : (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k).pre = some "LeafBlock43" :=
        wsStopAt_pre43 G _ (v := v.toNat) hik h13
      exact ⟨1, by omega, wsSeamSeg G C _ hsegRun.inv' hpre
        (by decide) heeSl hendsl h8sl hbitsl⟩
    · have hpre : (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k).pre = some "LeafBlock46" :=
        wsStopAt_pre46 G _ (v := v.toNat) hik h13 h32
      exact ⟨1, by omega, wsSeamSeg G C _ hsegRun.inv' hpre
        (by decide) heeSl hendsl h8sl hbitsl⟩
    · have hpre : (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k).pre = some "LeafBlock48" :=
        wsStopAt_pre48 G _ (v := v.toNat) hik h13 h32
      exact ⟨1, by omega, wsSeamSeg G C _ hsegRun.inv' hpre
        (by decide) heeSl hendsl h8sl hbitsl⟩
  obtain ⟨seam, hseam, hsegSeam⟩ := hSeam
  refine ⟨j + first + n + seam, by omega, ?_, hcondSl⟩
  exact ((hEntry.trans hsegFirst).trans hsegRun).trans hsegSeam

/-! ### The price

`n ≤ 5(k - i) + 10` and `8·(v - 1 - k)` against `8·(entryPos (C.k+1) - entryPos C.k)`, with
the run's start at or after this entry's position (`hstart`) and its stop before the next
entry's (`hspan`).  The `+5` is the entry allowance's spare, and the constant does not move. -/

theorem wsPrice {n k i vN a0 a1 : Nat}
    (hn : n ≤ 5 * (k - i) + 10) (hik : i < k) (hkv : k < vN)
    (hstart : a0 ≤ i) (hspan : vN ≤ a1) :
    n + stage2ByteAllowance * (vN - 1 - k) ≤
      stage2ByteAllowance * (a1 - a0) + 5 := by
  simp only [stage2ByteAllowance]
  omega

/-! ### The run at an arbitrary check state

The run's segment was stated at `contLandS` — the class-C route's byte-between-the-entries
check state — because that is what `contPrefixLand`'s eight links reach.  The run itself
reads only cells at its source: `%35` (the byte before the entry's end), `%idxprom.i`,
`%cond350.i`, `%8`, and the invariant's `%end.i`.  So the segment exists from **any**
`NodeBlock41` state whose cells are the document's, and the default head-switch classes
reach their own such state, `contLandOut (contMidS C q5 …) v b35`.

The layer below states that once: the pivot states as total functions of the source
(`wsP41Out`, `wsP39Out`, `wsP37Out`), the preheader and the stop (`wsPreSAt`, `wsSlAt`),
the three entry dispatches (`wsEntryAt33/35/37`), the composition around `wsRun`
(`contWsAfterPreAt`), the three arms (`contWsRunAt33/35/37`) and the arm-independent
bundle (`HcontRunFacts`) with the run derived from it (`contWsRunF`).

At `contLandS` the generic preheader and stop are `wsPreS` and `wsSlS`
(`wsPreSAt_transport`, `wsSlAt_transport`), so the class-C route is their instance and the
consumers' terms do not change. -/

/-- `NodeBlock41`'s target on the arm its `%35 < 13` test does not take: the pivot's
cell, at `NodeBlock39`.  The generic twin of `contP41S`, whose source is the check state
rather than the head's cells. -/
def wsP41Out (s : State) (b : UInt8) : State :=
  { (s.bind "%Pivot42" (.int 1 (evalICmp .slt (cont35 b) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some s.pc }

/-- `NodeBlock39`'s target on the arm its `%35 < 32` test takes: the pivot's cell, at
`LeafBlock35`. -/
def wsP39Out (s : State) (b : UInt8) : State :=
  { (s.bind "%Pivot40" (.int 1 (evalICmp .slt (cont35 b) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock35", pre := some s.pc }

/-- `NodeBlock39`'s target on the arm its `%35 < 32` test does not take: the same pivot's
cell, at `LeafBlock37`. -/
def wsP37Out (s : State) (b : UInt8) : State :=
  { (s.bind "%Pivot40" (.int 1 (evalICmp .slt (cont35 b) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock37", pre := some s.pc }

/-- **The preheader `%35`'s class selects**, as a total function of the check state and the
byte.  `wsPreS` is this at `contLandS`. -/
def wsPreSAt (sl : State) (b35 : UInt8) : State :=
  if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
    leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35)
  else if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
    leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35) (cont35 b35)
  else
    leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35) (cont35 b35)

/-- **The stop state the skip reaches**, as a total function of the check state and the
entry's numbers.  `wsSlS` is this at `contLandS`. -/
def wsSlAt {m0 : Mem} (G : WalkGeom m0) (sl : State) (b35 : UInt8) (ix : BitVec 64)
    (v : BitVec 32) (k : Nat) : State :=
  wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (wsPreSAt sl b35)) ix.toNat) ix.toNat
    v.toNat k

/-- The class-C route's pivot state is the generic one at its check state. -/
theorem wsP41Out_contLandS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    wsP41Out (contLandS C s x inc nep ep v ix b35) b35 =
      contP41S C s x inc nep ep v ix b35 := rfl

/-- The same at the second pivot. -/
theorem wsP39Out_contP41S {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    wsP39Out (wsP41Out (contLandS C s x inc nep ep v ix b35) b35) b35 =
      contP39S C s x inc nep ep v ix b35 := rfl

/-- The same at the second pivot's second arm. -/
theorem wsP37Out_contP41S {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    wsP37Out (wsP41Out (contLandS C s x inc nep ep v ix b35) b35) b35 =
      contP37S C s x inc nep ep v ix b35 := rfl

/-- `wsPreSAt` at the class-C route's check state is `wsPreS`. -/
theorem wsPreSAt_transport {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    wsPreSAt (contLandS C s x inc nep ep v ix b35) b35 =
      wsPreS G C s x inc nep ep v ix b35 := by
  simp only [wsPreSAt, wsPreS, wsP39Out_contP41S, wsP37Out_contP41S]

/-- `wsSlAt` at the class-C route's check state is `wsSlS`. -/
theorem wsSlAt_transport {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (k : Nat) :
    wsSlAt G (contLandS C s x inc nep ep v ix b35) b35 ix v k =
      wsSlS G C s x inc nep ep v ix b35 k := by
  simp only [wsSlAt, wsSlS, wsPreSAt_transport]

/-- `wsPreSAt` at `LeafBlock33`'s class is that arm's preheader state. -/
theorem wsPreSAt_33 (sl : State) (b35 : UInt8)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1) :
    wsPreSAt sl b35 = leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35) := by
  rw [wsPreSAt, if_pos hb13]

/-- `wsPreSAt` at `LeafBlock35`'s class is that arm's preheader state. -/
theorem wsPreSAt_35 (sl : State) (b35 : UInt8)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1) :
    wsPreSAt sl b35 =
      leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35) (cont35 b35) := by
  rw [wsPreSAt, if_neg (by rw [hb13]; decide), if_pos hb32]

/-- `wsPreSAt` at `LeafBlock37`'s class is that arm's preheader state. -/
theorem wsPreSAt_37 (sl : State) (b35 : UInt8)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0) :
    wsPreSAt sl b35 =
      leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35) (cont35 b35) := by
  rw [wsPreSAt, if_neg (by rw [hb13]; decide), if_neg (by rw [hb32]; decide)]

/-- The `%35` cell at the first pivot's target, in the form the next step reads. -/
theorem wsP41Out_35 (s : State) (b : UInt8)
    (h : lookupName s.env "%35" = some (.int 8 (cont35 b))) :
    lookupName (wsP41Out s b).env "%35" = some (.int 8 (cont35 b)) := by
  show lookupName (("%Pivot42", Value.int 1 (evalICmp IPred.slt (cont35 b)
    (BitVec.ofNat 8 13))) :: s.env) "%35" = some (.int 8 (cont35 b))
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The `%35` cell at the second pivot's target. -/
theorem wsP39Out_35 (s : State) (b : UInt8)
    (h : lookupName s.env "%35" = some (.int 8 (cont35 b))) :
    lookupName (wsP39Out s b).env "%35" = some (.int 8 (cont35 b)) := by
  show lookupName (("%Pivot40", Value.int 1 (evalICmp IPred.slt (cont35 b)
    (BitVec.ofNat 8 32))) :: s.env) "%35" = some (.int 8 (cont35 b))
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The `%35` cell at the second pivot's other arm. -/
theorem wsP37Out_35 (s : State) (b : UInt8)
    (h : lookupName s.env "%35" = some (.int 8 (cont35 b))) :
    lookupName (wsP37Out s b).env "%35" = some (.int 8 (cont35 b)) := by
  show lookupName (("%Pivot40", Value.int 1 (evalICmp IPred.slt (cont35 b)
    (BitVec.ofNat 8 32))) :: s.env) "%35" = some (.int 8 (cont35 b))
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **The run at `LeafBlock33`'s entry class**, at any check state. -/
theorem wsEntryAt33 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8)
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    WalkSegment calls G (ContAC₄ C) sl { C with block := "land.rhs.i.preheader" }
      (leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35)) 2 := by
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G (ContAC₄ C) sl hInv rfl h35
  have hres : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "LeafBlock33" := if_pos hb13
  have hst : s₁ = nodeBlock41OutAt sl (cont35 b35) := by
    rw [hs₁, hres]; rfl
  rw [hst] at hl₁
  rw [hres] at hl₁
  have h35' : lookupName (nodeBlock41OutAt sl (cont35 b35)).env "%35" =
      some (.int 8 (cont35 b35)) := by
    show lookupName (("%Pivot42", .int 1 (evalICmp .slt (cont35 b35)
      (BitVec.ofNat 8 13))) :: sl.env) "%35" = some (.int 8 (cont35 b35))
    rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h35
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.LeafBlock33_at (calls := calls) G { ContAC₄ C with block := "LeafBlock33" }
      (nodeBlock41OutAt sl (cont35 b35)) hl₁.inv' rfl h35'
  have hres2 : (if evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 then "land.rhs.i.preheader" else "if.end372.i") =
      "land.rhs.i.preheader" := if_pos hws
  have hst2 : s₂ = leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35) := by
    rw [hs₂, hres2]; rfl
  rw [hst2] at hl₂
  rw [hres2] at hl₂
  exact (WalkSegment.of_link hl₁).trans (WalkSegment.of_link hl₂)

/-- **The entry dispatch at `LeafBlock35`'s class**, at any check state: three links. -/
theorem wsEntryAt35 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8)
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbq13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) :
    WalkSegment calls G (ContAC₄ C) sl { C with block := "land.rhs.i.preheader" }
      (leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35) (cont35 b35)) 3 := by
  have h35l : lookupName sl.env "%35" = some (.int 8 (cont35 b35)) := by
    simpa only [evalOperand] using h35
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G (ContAC₄ C) sl hInv rfl h35
  have hres : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
  have hst : s₁ = wsP41Out sl b35 := by
    rw [hs₁, hres]; rfl
  rw [hst] at hl₁
  rw [hres] at hl₁
  have h35b : evalOperand (wsP41Out sl b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact wsP41Out_35 sl b35 h35l
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock39_at (calls := calls) G (ContAC₅ C) (wsP41Out sl b35) hl₁.inv' rfl h35b
  have hres2 : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
      "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := if_pos hb32
  have hst2 : s₂ = wsP39Out (wsP41Out sl b35) b35 := by
    rw [hs₂, hres2]; rfl
  rw [hst2] at hl₂
  rw [hres2] at hl₂
  have h35c : evalOperand (wsP39Out (wsP41Out sl b35) b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact wsP39Out_35 (wsP41Out sl b35) b35 (wsP41Out_35 sl b35 h35l)
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock35_at (calls := calls) G (ContAC₆ C)
      (wsP39Out (wsP41Out sl b35) b35) hl₂.inv' rfl h35c
  have hres3 : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "land.rhs.i.preheader" else "if.end372.i") = "land.rhs.i.preheader" :=
    if_pos hbq13
  have hst3 : s₃ = leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35) (cont35 b35) := by
    rw [hs₃, hres3]; rfl
  rw [hst3] at hl₃
  rw [hres3] at hl₃
  exact ((WalkSegment.of_link hl₁).trans (WalkSegment.of_link hl₂)).trans
    (WalkSegment.of_link hl₃)

/-- **The entry dispatch at `LeafBlock37`'s class**, at any check state: three links. -/
theorem wsEntryAt37 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8)
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbq32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1) :
    WalkSegment calls G (ContAC₄ C) sl { C with block := "land.rhs.i.preheader" }
      (leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35) (cont35 b35)) 3 := by
  have h35l : lookupName sl.env "%35" = some (.int 8 (cont35 b35)) := by
    simpa only [evalOperand] using h35
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock41_at (calls := calls) G (ContAC₄ C) sl hInv rfl h35
  have hres : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
  have hst : s₁ = wsP41Out sl b35 := by
    rw [hs₁, hres]; rfl
  rw [hst] at hl₁
  rw [hres] at hl₁
  have h35b : evalOperand (wsP41Out sl b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact wsP41Out_35 sl b35 h35l
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock39_at (calls := calls) G (ContAC₅ C) (wsP41Out sl b35) hl₁.inv' rfl h35b
  have hres2 : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
      "LeafBlock35" else "LeafBlock37") = "LeafBlock37" := by rw [hb32]; rfl
  have hst2 : s₂ = wsP37Out (wsP41Out sl b35) b35 := by
    rw [hs₂, hres2]; rfl
  rw [hst2] at hl₂
  rw [hres2] at hl₂
  have h35c : evalOperand (wsP37Out (wsP41Out sl b35) b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact wsP37Out_35 (wsP41Out sl b35) b35 (wsP41Out_35 sl b35 h35l)
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock37_at (calls := calls) G { ContAC₅ C with block := "LeafBlock37" }
      (wsP37Out (wsP41Out sl b35) b35) hl₂.inv' rfl h35c
  have hres3 : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1 then
      "land.rhs.i.preheader" else "if.end372.i") = "land.rhs.i.preheader" :=
    if_pos hbq32
  have hst3 : s₃ = leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35) (cont35 b35) := by
    rw [hs₃, hres3]; rfl
  rw [hst3] at hl₃
  rw [hres3] at hl₃
  exact ((WalkSegment.of_link hl₁).trans (WalkSegment.of_link hl₂)).trans
    (WalkSegment.of_link hl₃)

/-! #### The cells the generic states keep

Each pivot binds one cell in front of its source's environment and the preheader's leaves
bind their own, so the cells the run reads are the check state's.  The names are the run's
own (`%35`, `%idxprom.i`, `%cond350.i`, `%end.i`), so each peel is `lookupName_cons_ne` at
a literal; the `%35` peels are above, beside the dispatches that read them. -/

/-- **`%cond350.i` at the preheader is the check state's**: neither the pivots nor the
leaves bind it. -/
theorem wsPreSAt_cond (sl : State) (b35 : UInt8) :
    lookupName (wsPreSAt sl b35).env "%cond350.i" = lookupName sl.env "%cond350.i" := by
  simp only [wsPreSAt]
  split
  · simp only [leafBlock33OutAt, nodeBlock41OutAt, stateAt, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [leafBlock35OutAt, wsP39Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [leafBlock37OutAt, wsP37Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **`%idxprom.i` at the preheader is the check state's**, for the same reason. -/
theorem wsPreSAt_idx (sl : State) (b35 : UInt8) :
    lookupName (wsPreSAt sl b35).env "%idxprom.i" = lookupName sl.env "%idxprom.i" := by
  simp only [wsPreSAt]
  split
  · simp only [leafBlock33OutAt, nodeBlock41OutAt, stateAt, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [leafBlock35OutAt, wsP39Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [leafBlock37OutAt, wsP37Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The preheader keeps the static register. -/
theorem wsPreSAt_envEnd (sl : State) (b35 : UInt8) :
    lookupName (wsPreSAt sl b35).env "%end.i" = lookupName sl.env "%end.i" := by
  simp only [wsPreSAt]
  split
  · simp only [leafBlock33OutAt, nodeBlock41OutAt, stateAt, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [leafBlock35OutAt, wsP39Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [leafBlock37OutAt, wsP37Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The stop state keeps the static register, at any check state. -/
theorem wsSlAt_envEnd {m0 : Mem} (G : WalkGeom m0) (sl : State) (b35 : UInt8)
    (ix : BitVec 64) (v : BitVec 32) (k : Nat) :
    lookupName (wsSlAt G sl b35 ix v k).env "%end.i" = lookupName sl.env "%end.i" := by
  simp only [wsSlAt]
  rw [wsStopAt_envEnd, wsLeafS_envEnd]
  exact wsPreSAt_envEnd sl b35

/-- **The seam's `%8` is its source's**, at any source: the seam binds five cells and none
of them is `%8`. -/
theorem contWsSeamS_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sl : State)
    (k : Nat) (b8 : BitVec 8)
    (h : evalOperand (contWsSeamS C sl k b8) (.reg "%8") = some (.int 8 b8)) :
    lookupName sl.env "%8" = some (.int 8 b8) := by
  simp only [contWsSeamS, seamS, seamFin, stateAt, evalOperand] at h
  repeat rw [lookupName_cons_ne _ _ (by decide)] at h
  exact h

/-- **The skip keeps `%8`**: every state it passes binds its own cells, and `%8` is not
one of them.  So the byte the seam tests is the check state's byte, which the invariant
carries — the bridge `hcontRunFacts_x1` uses. -/
theorem scanLatchOut_env8 (s : State) (i c : Nat) (t : String) :
    lookupName (scanLatchOut s "%inc371.i" "%exitcond.not" i c t).env "%8" =
      lookupName s.env "%8" := by
  simp only [scanLatchOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `wsLeafS` at either class keeps `%8`. -/
theorem wsLeafS_env8 {m0 : Mem} (G : WalkGeom m0) (s : State) (p : Nat) :
    lookupName (wsLeafS G s p).env "%8" = lookupName s.env "%8" := by
  simp only [wsLeafS]
  split
  · simp only [leafBlock43OutAt, nodeBlock52OutAt, wsLandS, landRhsIOutAt, stateAt, cells,
      State.bind, State.bindAll]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [scanNodeBlock50In, wsLandS, landRhsIOutAt, stateAt, cells, State.bind,
        State.bindAll]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [scanNodeBlock50In, wsLandS, landRhsIOutAt, stateAt, cells, State.bind,
        State.bindAll]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The latch at `n` visits keeps `%8`. -/
theorem wsLatchAt_env8 {m0 : Mem} (G : WalkGeom m0) (l : State) (i v : Nat) :
    ∀ n, lookupName (wsLatchAt G l i v n).env "%8" = lookupName l.env "%8"
  | 0 => rfl
  | n + 1 => by
    simp only [wsLatchAt]
    rw [wsLeafS_env8, scanLatchOut_env8, wsLatchAt_env8 G l i v n]

/-- The stop state keeps `%8`, whichever leaf stopped the skip. -/
theorem wsStopAt_env8 {m0 : Mem} (G : WalkGeom m0) (l : State) (i v k : Nat) :
    lookupName (wsStopAt G l i v k).env "%8" = lookupName l.env "%8" := by
  unfold wsStopAt
  split
  · rfl
  · simp only [wsStopS]
    rw [wsLeafS_env8, scanLatchOut_env8, wsLatchAt_env8]

/-- The preheader keeps `%8`. -/
theorem wsPreSAt_env8 (sl : State) (b35 : UInt8) :
    lookupName (wsPreSAt sl b35).env "%8" = lookupName sl.env "%8" := by
  simp only [wsPreSAt]
  split
  · simp only [leafBlock33OutAt, nodeBlock41OutAt, stateAt, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  · split
    · simp only [leafBlock35OutAt, wsP39Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    · simp only [leafBlock37OutAt, wsP37Out, wsP41Out, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **The stop state keeps `%8`**, at any check state. -/
theorem wsSlAt_env8 {m0 : Mem} (G : WalkGeom m0) (sl : State) (b35 : UInt8)
    (ix : BitVec 64) (v : BitVec 32) (k : Nat) :
    lookupName (wsSlAt G sl b35 ix v k).env "%8" = lookupName sl.env "%8" := by
  simp only [wsSlAt]
  rw [wsStopAt_env8, wsLeafS_env8]
  exact wsPreSAt_env8 sl b35

/-- **The check state's run landing keeps `%cond350.i`**: the preheader's cell is the check
state's, and the skip's states above it bind nothing of that name.  The run's tail reads the
copy call's bound at the byte's leaf, so this is the transport that makes the lane's word
available there. -/
theorem wsSlAt_cond {m0 : Mem} (G : WalkGeom m0) (sl : State) (b35 : UInt8)
    (ix : BitVec 64) (v : BitVec 32) (k : Nat) :
    lookupName (wsSlAt G sl b35 ix v k).env "%cond350.i" = lookupName sl.env "%cond350.i" := by
  simp only [wsSlAt]
  rw [wsStopAt_cond, wsLeafS_cond]
  exact wsPreSAt_cond sl b35

/-! ### The three arms

Each applies its entry dispatch and hands the result to `contWsAfterPreAt`.  The preheader's
two cells (`%idxprom.i`, `%cond350.i`) are the check state's, which the peels above read. -/

/-- **The run at `LeafBlock33`'s entry class**, at any check state. -/
theorem contWsRunAt33 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) {ix : BitVec 64} {v : BitVec 32} {k : Nat} {b8 : BitVec 8}
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hidx0 : lookupName sl.env "%idxprom.i" = some (.int 64 ix))
    (hcond0 : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
      (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
      (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl (ContSeamC C)
        (contWsSeamS C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
          (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k)
          k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  have hpre := wsPreSAt_33 sl b35 hb13
  have hidx : lookupName (leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35))
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
    rw [← hpre, wsPreSAt_idx]; exact hidx0
  have hcond : lookupName (leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35))
      (cont35 b35)).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rw [← hpre, wsPreSAt_cond]; exact hcond0
  exact contWsAfterPreAt G C sl v ix _ (j := 2)
    (wsEntryAt33 G C sl b35 hInv h35 hb13 hws) (by omega)
    rfl hidx hcond hiv hvsub hcw hi63 hgn hik hkv hcontI hcls hstop hpos hqn halen hevlen
    h8sl hendsl hbitsl

/-- **The run at `LeafBlock35`'s entry class**, at any check state. -/
theorem contWsRunAt35 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) {ix : BitVec 64} {v : BitVec 32} {k : Nat} {b8 : BitVec 8}
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbq13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hidx0 : lookupName sl.env "%idxprom.i" = some (.int 64 ix))
    (hcond0 : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
      (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
      (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl (ContSeamC C)
        (contWsSeamS C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
          (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k)
          k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  have hpre := wsPreSAt_35 sl b35 hb13 hb32
  have hidx : lookupName (leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
    rw [← hpre, wsPreSAt_idx]; exact hidx0
  have hcond : lookupName (leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rw [← hpre, wsPreSAt_cond]; exact hcond0
  exact contWsAfterPreAt G C sl v ix _ (j := 3)
    (wsEntryAt35 G C sl b35 hInv h35 hb13 hb32 hbq13) (by omega)
    rfl hidx hcond hiv hvsub hcw hi63 hgn hik hkv hcontI hcls hstop hpos hqn halen hevlen
    h8sl hendsl hbitsl

/-- **The run at `LeafBlock37`'s entry class**, at any check state. -/
theorem contWsRunAt37 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) {ix : BitVec 64} {v : BitVec 32} {k : Nat} {b8 : BitVec 8}
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbq32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hidx0 : lookupName sl.env "%idxprom.i" = some (.int 64 ix))
    (hcond0 : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
      (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
      (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl (ContSeamC C)
        (contWsSeamS C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
          (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k)
          k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  have hpre := wsPreSAt_37 sl b35 hb13 hb32
  have hidx : lookupName (leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
    rw [← hpre, wsPreSAt_idx]; exact hidx0
  have hcond : lookupName (leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rw [← hpre, wsPreSAt_cond]; exact hcond0
  exact contWsAfterPreAt G C sl v ix _ (j := 3)
    (wsEntryAt37 G C sl b35 hInv h35 hb13 hb32 hbq32) (by omega)
    rfl hidx hcond hiv hvsub hcw hi63 hgn hik hkv hcontI hcls hstop hpos hqn halen hevlen
    h8sl hendsl hbitsl

/-- **The run class's bundle, at any check state.**

`HcontFacts`'s run-relevant part with the head's cells removed: the check state's two
cells (`%35`, `%idxprom.i`), the bound and the entry's index, the class bits and the
traversal class, the stop and the seam's byte, the tail's three calls, the landing and the
scan's traversal.  The check state is the structure's index, so the bundle is stated once
for every class that reaches a `NodeBlock41` check: the class-C route's `contLandS` and
each default class's `contLandOut (contMidS C q5 …) v b35` alike.  The last two class
conjuncts are the inner budget the first visit's `ScanEntered` needs and the `entryPos`
fact the price's `+5` rests on; they are properties of the entry, not of the head class. -/
structure HcontRunFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State) : Type where
  /-- The check state's own invariant, at the byte's dispatch. -/
  hInv : WalkInv G (ContAC₄ C) sl
  /-- The byte before the entry's end, as the check reads it. -/
  b35 : UInt8
  h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35))
  /-- The entry's index, as the head switch left it, and the entry's end. -/
  ix : BitVec 64
  hidx : lookupName sl.env "%idxprom.i" = some (.int 64 ix)
  v : BitVec 32
  hcond : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  /-- The entry is not empty: `%cond350.i` is above `%idxprom.i`. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The whitespace skip's stop, its byte and the traversal class.**  `%35` is one of
  the four whitespace bytes (the three disjuncts), every byte the skip reads continues the
  token until `k`, and `k` stops it. -/
  k : Nat
  x1 : BitVec 8
  hClass :
    ((evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)) ∧
    (∀ q, ix.toNat ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧ ix.toNat < k ∧
    v.toNat - ix.toNat ≤ C.inner ∧ entryPos G C.k ≤ ix.toNat
  /-- The run's stop is inside the entry. -/
  heicd : k < v.toNat
  /-- The entry's first byte's class, read at the seam's name, and the byte test's clear
  arm — the arm that leaves `if.end372.i` for `if.else387.i`.  **Not** the class-C span's
  premises (`slt x1 110`, `slt x1 116`, `≠ 116`): those pin the byte to `[110, 128)` and
  belong to the class that composes the span, not to the run. -/
  h8c : evalOperand (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) (.reg "%8") =
    some (.int 8 x1)
  hbit : (evalICmp .eq x1 (BitVec.ofNat 8 45) |||
    evalICmp .ult (x1 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The tail's own: its three call outcomes, the event it emits, and its segment from
  the class-C span's target to the scan's entry — `consumerTailSegAt` at count `3`, its
  first index the run's stop `k` and its bound the lane's word. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
    (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)
    (TailCarryScan (ContTailStartC C) ev)
    (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA) 3
  /-- The scan's landing: the byte's address and the byte.  The index is `k` — the seam's
  stored end — everywhere the landing's states name it. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA).env
    "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
    (landRhs457OutAt (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q) (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
    (ScanS₉₆ (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (contWsLatch C (wsSlAt G sl b35 ix v k) k x1 x1 r₁ r₂ r₃ k v cA rdv xA
      (BitVec.ofNat 64 k) a q x47)
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and the run's stop at or after this one's. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ k
  /-- **The traversal's round**: `walkScanRounds457_of_cell`'s `hround`, unweakened. -/
  hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
    (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    p + 1 < v.toNat → p + 1 < 2 ^ 63 →
    lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i").env
      "%3" = some (.ptr a) →
    readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
    evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
      "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
    evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
    evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
    WalkLocal (ScanC₁₀₅ (ScanCLand C'))
      (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) →
    WalkLocal (ScanC₉₆ (ScanCLand C'))
      (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    WalkLocal { ScanCLand C' with block := "while.body462.i" }
      (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
      WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  /-- **The input's totality at every index the scan visits**: `walkScanRounds457_of_cell`'s
  `hbyte` at the visits' span.  The lower bound `k < p + 1` is the run's stop, so the row
  says nothing about the entry's token prefix, which `hClass` makes non-whitespace. -/
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
    C'.block = "while.body462.i" → k < p + 1 → p + 1 < v.toNat →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i").env "%3" = some (.ptr a) ∧
      readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) ∧
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x)
  /-- **The token record's register at the scan's exit**, at the states the traversal's
  counters pin: a traversal whose final state is existential has no named term to state a
  register at. -/
  htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok)

/-- **The run's own rows at a check state**, without the bundle's tail.  This is
`HcontRunFacts` minus every field the run's derivation does not read: its segment, count
and stop cell follow from these alone (`contWsRunBody`), so the seam's invariant can be
obtained without the tail the seam is used to produce.  The fields are exactly
`contWsRunF`'s read set. -/
structure HcontRunBody {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State) : Type where
  hInv : WalkInv G (ContAC₄ C) sl
  b35 : UInt8
  h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35))
  ix : BitVec 64
  hidx : lookupName sl.env "%idxprom.i" = some (.int 64 ix)
  v : BitVec 32
  hcond : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  k : Nat
  x1 : BitVec 8
  hClass :
    ((evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)) ∧
    (∀ q, ix.toNat ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧ ix.toNat < k ∧
    v.toNat - ix.toNat ≤ C.inner ∧ entryPos G C.k ≤ ix.toNat
  heicd : k < v.toNat
  h8c : evalOperand (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) (.reg "%8") =
    some (.int 8 x1)
  hbit : (evalICmp .eq x1 (BitVec.ofNat 8 45) |||
    evalICmp .ult (x1 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  hspan : v.toNat ≤ entryPos G (C.k + 1)

/-- **The run's segment, from its own rows.**  The three arms of `%35`'s class give the
source; `contWsRunAt33/35/37` gives the segment, its count bound and the stop's
`%cond350.i` cell.  Nothing here reads the bundle's tail: this is the derivability the
seam group needs, and `contWsRunF` is its instance at `HcontRunFacts`. -/
theorem contWsRunBody {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (b : HcontRunBody G C sl) (hk : C.k + 1 < G.nep) :
    ∃ N, N ≤ 5 * (b.k - b.ix.toNat) + 10 ∧
      WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C) sl (ContSeamC C)
        (contWsSeamS C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1) N ∧
      lookupName (wsSlAt G sl b.b35 b.ix b.v b.k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 b.v.toNat)) := by
  obtain ⟨hcase, hcls, hstop, hik, hvsub, -⟩ := b.hClass
  have hiv : b.ix.toNat < b.v.toNat := by
    have h := (evalICmp_ugt_one_iff_toNat (BitVec.ofNat 64 b.v.toNat) b.ix).1 b.hugt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.v.isLt; omega)] at h
    exact h
  have hcw : b.v.toNat < 2 ^ 64 := by have := b.v.isLt; omega
  have hposE : entryPos G (C.k + 1) < G.n := entryPos_lt G hk
  have hgn : b.ix.toNat < G.n := by have := b.hspan; omega
  have hi63 : b.ix.toNat < 2 ^ 63 := by
    have h1 := G.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hpos : ∀ q, b.ix.toNat < q → q ≤ b.k → q < 2 ^ 63 := by
    intro q h1 h2
    have h1' := G.maxDoc
    simp only [stage2MaxDocument] at h1'
    have h4 : b.k < b.v.toNat := b.heicd
    have h5 : b.v.toNat ≤ entryPos G (C.k + 1) := b.hspan
    have h6 := hposE
    have h7 : q < G.n := by omega
    omega
  have hqn : ∀ q, b.ix.toNat < q → q ≤ b.k → q < G.n := by
    intro q h1 h2
    have h4 : b.k < b.v.toNat := b.heicd
    have h5 : b.v.toNat ≤ entryPos G (C.k + 1) := b.hspan
    omega
  have halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve := by
    have h := b.hInv.alen_le
    change C.alen ≤ G.ndst0 + G.n at h
    omega
  have hevlen : C.evlen ≤ G.evcap := by
    have h1 := b.hInv.evlen_le
    change C.evlen ≤ G.nev0 + stage2RecordBytes * G.n at h1
    have h2 := G.evRoom
    omega
  have hcontI : wsCont G b.ix.toNat := hcls b.ix.toNat le_rfl hik
  have hcls' : ∀ q, b.ix.toNat < q → q < b.k → wsCont G q :=
    fun q h1 h2 => hcls q (by omega) h2
  have hbitsl : (evalICmp .eq b.x1 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b.x1 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := b.hbit
  have h8sl : lookupName (wsSlAt G sl b.b35 b.ix b.v b.k).env "%8" = some (.int 8 b.x1) :=
    contWsSeamS_env8 C _ b.k b.x1 b.h8c
  -- the seam's stored end is the check state's static register
  have hendsl : lookupName (wsSlAt G sl b.b35 b.ix b.v b.k).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) := by
    rw [wsSlAt_envEnd]
    exact b.hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  rcases hcase with ⟨hb13, hws⟩ | ⟨hb13, hb32, hbq13⟩ | ⟨hb13, hb32, hbq32⟩
  · have hpre := wsPreSAt_33 sl b.b35 hb13
    have h8sl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt sl (cont35 b.b35)) (cont35 b.b35))) b.ix.toNat) b.ix.toNat
        b.v.toNat b.k).env "%8" = some (.int 8 b.x1) := by
      simpa only [wsSlAt, hpre] using h8sl
    have hendsl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt sl (cont35 b.b35)) (cont35 b.b35))) b.ix.toNat) b.ix.toNat
        b.v.toNat b.k).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
      simpa only [wsSlAt, hpre] using hendsl
    simpa only [wsSlAt, hpre] using
      (contWsRunAt33 (calls := stage2Calls stage2SubCalls) G C sl b.b35 b.hInv b.h35 hb13 hws
        b.hidx b.hcond hiv hvsub hcw hi63 hgn hik b.heicd hcontI hcls' hstop hpos hqn
        halen hevlen h8sl' hendsl' hbitsl)
  · have hpre := wsPreSAt_35 sl b.b35 hb13 hb32
    have h8sl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (wsP39Out (wsP41Out sl b.b35) b.b35) (cont35 b.b35))) b.ix.toNat) b.ix.toNat
        b.v.toNat b.k).env "%8" = some (.int 8 b.x1) := by
      simpa only [wsSlAt, hpre] using h8sl
    have hendsl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (wsP39Out (wsP41Out sl b.b35) b.b35) (cont35 b.b35))) b.ix.toNat) b.ix.toNat
        b.v.toNat b.k).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
      simpa only [wsSlAt, hpre] using hendsl
    simpa only [wsSlAt, hpre] using
      (contWsRunAt35 (calls := stage2Calls stage2SubCalls) G C sl b.b35 b.hInv b.h35 hb13 hb32 hbq13
        b.hidx b.hcond hiv hvsub hcw hi63 hgn hik b.heicd hcontI hcls' hstop hpos hqn
        halen hevlen h8sl' hendsl' hbitsl)
  · have hpre := wsPreSAt_37 sl b.b35 hb13 hb32
    have h8sl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (wsP37Out (wsP41Out sl b.b35) b.b35) (cont35 b.b35))) b.ix.toNat) b.ix.toNat
        b.v.toNat b.k).env "%8" = some (.int 8 b.x1) := by
      simpa only [wsSlAt, hpre] using h8sl
    have hendsl' : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (wsP37Out (wsP41Out sl b.b35) b.b35) (cont35 b.b35))) b.ix.toNat) b.ix.toNat
        b.v.toNat b.k).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
      simpa only [wsSlAt, hpre] using hendsl
    simpa only [wsSlAt, hpre] using
      (contWsRunAt37 (calls := stage2Calls stage2SubCalls) G C sl b.b35 b.hInv b.h35 hb13 hb32 hbq32
        b.hidx b.hcond hiv hvsub hcw hi63 hgn hik b.heicd hcontI hcls' hstop hpos hqn
        halen hevlen h8sl' hendsl' hbitsl)

/-- **The run's segment, from the bundle's class field.**  `contWsRunBody` at the fields the
segment reads; the bundle's tail is not among them, which is what lets the seam's invariant
be derived before the tail is built. -/
theorem contWsRunF {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (f : HcontRunFacts G C sl) (hk : C.k + 1 < G.nep) :
    ∃ N, N ≤ 5 * (f.k - f.ix.toNat) + 10 ∧
      WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C) sl (ContSeamC C)
        (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) N ∧
      lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 f.v.toNat)) :=
  contWsRunBody G C sl
    { hInv := f.hInv, b35 := f.b35, h35 := f.h35, ix := f.ix, hidx := f.hidx, v := f.v,
      hcond := f.hcond, hugt := f.hugt, k := f.k, x1 := f.x1, hClass := f.hClass,
      heicd := f.heicd, h8c := f.h8c, hbit := f.hbit, hspan := f.hspan } hk

/-- **The run's price, from the bundle.**  `wsPrice` at the class field's start fact and the
span's end. -/
theorem contWsPriceAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (f : HcontRunFacts G C sl) {N : Nat} (hN : N ≤ 5 * (f.k - f.ix.toNat) + 10) :
    N + stage2ByteAllowance * (f.v.toNat - 1 - f.k) ≤
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5 :=
  wsPrice hN f.hClass.2.2.2.1 f.heicd f.hClass.2.2.2.2.2 f.hspan

/-! #### The class-C route's check state's cells, and its bundle

`contLandS`'s two cells the bundle states are the head state's: `%35` is the byte the
check bound, `%idxprom.i` is the head switch's index and `%cond350.i` is
`cond.end349.i`'s store.  Peeling `contLandS` and `contEndS`'s own cells leaves the
`contAS₅` state's. -/

/-- `%idxprom.i` at the class-C route's check state is `cond.true345.i`'s. -/
theorem contLandS_idx {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contLandS C s x inc nep ep v ix b35).env "%idxprom.i" =
      lookupName (contAS₅ s x inc nep).env "%idxprom.i" := by
  simp only [contLandS, contEndS, condEnd349OutAt, cte345OutAt, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the class-C route's check state is the entry's end. -/
theorem contLandS_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contLandS C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact contEndS_cond C s x inc nep ep v ix

/-- **The class-C route's bundle, from `HcontFacts` and its check state's invariant.**
Every field is `HcontFacts`'s own, transported from `wsSlS` to `wsSlAt` at the check
state; the check state's two cells are its peels. -/
noncomputable def hcontRunFacts_of_contFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (f : HcontFacts G C s)
    (hInv : WalkInv G (ContAC₄ C) (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35)) :
    HcontRunFacts G C (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) where
  hInv := hInv
  b35 := f.b35
  h35 := by
    simp only [evalOperand]
    exact contLandS_35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35
  ix := f.ix
  hidx := by
    rw [contLandS_idx]
    exact f.hidx5
  v := f.v
  hcond := contLandS_cond C s f.x f.inc f.nep f.ep f.v f.ix f.b35
  hugt := f.hugt
  k := f.k
  x1 := f.x1
  hClass := f.hClass
  heicd := f.heicd
  h8c := by
    rw [wsSlAt_transport]
    exact f.h8c
  hbit := wsBit45 f.hc110
  r₁ := f.r₁
  r₂ := f.r₂
  r₃ := f.r₃
  ev := f.ev
  cA := f.cA
  rdv := f.rdv
  xA := f.xA
  hTail := by
    rw [wsSlAt_transport]
    exact f.hTail
  a := f.a
  q := f.q
  bs := f.bs
  h3S := by
    rw [wsSlAt_transport]
    exact f.h3S
  hpos := f.hpos
  hreadS := by
    rw [wsSlAt_transport]
    exact f.hreadS
  hbsS := f.hbsS
  hloc105 := by
    rw [wsSlAt_transport]
    exact f.hloc105
  x47 := f.x47
  h47 := by
    rw [wsSlAt_transport]
    exact f.h47
  hbit47 := f.hbit47
  hws47 := f.hws47
  hloc96 := by
    rw [wsSlAt_transport]
    exact f.hloc96
  hlatch := by
    rw [wsSlAt_transport]
    exact f.hlatch
  hspan := f.hspan
  hstart := f.hstart
  hround := f.hround
  hbyte := f.hbyte
  htok := f.htok

/-! #### The bundle's own states, and the byte bridge

The scan's entry and latch at the bundle's own terms (as `contWsEntryF`/`contWsLatchF` are
at `HcontFacts`'s), the peels the landing and the scan's cells need, and the bridge that
makes the seam's byte the head's: `%8` is loaded once and the skip keeps it, so `x1` is
`hlastByte G C`. -/

/-- The scan's entry, at the bundle's own terms. -/
abbrev contWsEntryAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) : State :=
  contWsEntry C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 f.x1 f.r₁ f.r₂ f.r₃ f.k f.v
    f.cA f.rdv f.xA

/-- The scan's latch, at the bundle's own terms. -/
abbrev contWsLatchAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) : State :=
  contWsLatch C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 f.x1 f.r₁ f.r₂ f.r₃ f.k f.v
    f.cA f.rdv f.xA (BitVec.ofNat 64 f.k) f.a f.q f.x47

/-- **The seam's byte is the head's byte.**  `f.h8c` reads the seam's `%8` as `x1`, the
skip keeps `%8` (`wsSlAt_env8`), and the check state's invariant carries it as
`hlastByte G C`. -/
theorem hcontRunFacts_x1 {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) : f.x1 = hlastByte G C := by
  have h1 : lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%8" = some (.int 8 f.x1) :=
    contWsSeamS_env8 C _ f.k f.x1 f.h8c
  have h3 : lookupName sl.env "%8" = some (.int 8 (hlastByte G C)) := by
    simpa only [hlastByte] using f.hInv.iter.reg8
  rw [wsSlAt_env8, h3] at h1
  have h2 : (Value.int 8 (hlastByte G C)) = (Value.int 8 f.x1) := Option.some.inj h1
  have hval : (hlastByte G C).toNat = f.x1.toNat := by
    have := congrArg (fun v => match v with
      | .int _ b => BitVec.toNat b
      | _ => 0) h2
    simpa using this
  exact (BitVec.eq_of_toNat_eq hval).symm

/-- The scan's entry's predecessor is the copy call's block, at the bundle. -/
theorem contWsEntryAt_pre {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) : (contWsEntryAt f).pre = some "if.then447.i" := by
  simp only [contWsEntryAt, contWsEntry, ScanEntry, TailS₃]

/-- **`hopS` is produced at the bundle.**  The seam stored the run's stop `k` in `%ee.1.i`
and the scan's entry `phi` selects that cell on `if.then447.i`'s edge, so the landing's
index *is* the run's stop. -/
theorem contWsEntryAt_hopS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) :
    evalOperand (stateAt (contWsEntryAt f).env (contWsEntryAt f)) (.reg "%ee.1.i") =
      some (.int 64 (BitVec.ofNat 64 f.k)) := by
  simp only [evalOperand, stateAt]
  exact contWsEntry_ee C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 f.x1 f.r₁ f.r₂ f.r₃
    f.k f.v f.cA f.rdv f.xA

/-- `%inc.i` at the bundle's latch is the run's endpoint's. -/
theorem contWsLatchAt_inc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) :
    lookupName (contWsLatchAt f).env "%inc.i" =
      lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%inc.i" := by
  simp only [contWsLatchAt, contWsLatch, Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut,
    contWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contWsTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the bundle's latch is the run's endpoint's. -/
theorem contWsLatchAt_nep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) :
    lookupName (contWsLatchAt f).env "%nep" =
      lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%nep" := by
  simp only [contWsLatchAt, contWsLatch, Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut,
    contWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contWsTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the bundle's latch is the lane's word. -/
theorem contWsLatchAt_cond {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl)
    (hcond : lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat))) :
    lookupName (contWsLatchAt f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := by
  simp only [contWsLatchAt, contWsLatch, Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut,
    contWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contWsTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hcond

/-- **The scan's landing, at the bundle's own entry.**  `walkScanLinks457`'s three links,
with the bundle's fields at every premise, and the latch named at `contWsLatchAt`. -/
theorem wsLandingSegAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sl : State}
    (f : HcontRunFacts G C sl) :
    WalkSegment (stage2Calls stage2SubCalls) G (TailCarryScan (ContTailStartC C) f.ev)
      (contWsEntryAt f) { TailCarryScan (ContTailStartC C) f.ev with
        block := "while.body462.i" } (contWsLatchAt f) 3 := by
  obtain ⟨s', hs', hseg⟩ :=
    walkScanLinks457 (calls := stage2Calls stage2SubCalls) (G := G)
      (C := TailCarryScan (ContTailStartC C) f.ev) (s := contWsEntryAt f) f.hTail.inv' rfl
      (contWsEntryAt_pre f) hlastEntry_phiSel (contWsEntryAt_hopS f) f.h3S f.hpos f.hreadS
      f.hbsS f.hloc105 f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  rw [hs'] at hseg
  exact hseg

/-! #### The run's head at a default class

`wsRunHeadAt` is the head chain `RunFacts` reads: the class's chain to the check state, the
run, and the seam's two cells.  The class's chain is `hPre` — its own prefix joined to
`contSwToLandSeg`'s four (`JsonStage2WalkDispatchLettersHead`, where the default arm's
states live). -/

/-- **The run class's head at a default class.**  The class's chain to the check state, the
run at its own count and the seam's two cells: `RunFacts`'s head, at `nPre + N` inside
`12 + N`. -/
structure WsRunHeadAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (sl : State) (nPre : Nat) (f : HcontRunFacts G C sl) : Type where
  N : Nat
  seg : WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
    (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) (nPre + N)
  hnH : nPre + N ≤ 12 + N
  h8 : evalOperand (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) (.reg "%8") =
    some (.int 8 (hlastByte G C))
  hcond : lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%cond350.i" =
    some (.int 64 (BitVec.ofNat 64 f.v.toNat))
  hprice : N + 8 * (f.v.toNat - 1 - f.k) ≤
    8 * (entryPos G (C.k + 1) - entryPos G C.k) + 5

/-- **The head chain at any class's check state.**  `hPre` is the class's own chain from
the loop head to the check state (at most eight links: the class's prefix and
`contSwToLandSeg`'s four), and the run is `contWsRunF`'s. -/
noncomputable def wsRunHeadAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (sl : State) (nPre : Nat)
    (hPre : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C) sl nPre)
    (hnPre : nPre ≤ 8) (f : HcontRunFacts G C sl) (hk : C.k + 1 < G.nep) :
    WsRunHeadAt G C s sl nPre f := by
  classical
  let hc := contWsRunF G C sl f hk
  let N := hc.choose
  have hspec := hc.choose_spec
  have hN : N ≤ 5 * (f.k - f.ix.toNat) + 10 := hspec.1
  have hrun : WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C) sl (ContSeamC C)
      (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) N := hspec.2.1
  have hcond : lookupName (wsSlAt G sl f.b35 f.ix f.v f.k).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := hspec.2.2
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) (nPre + N) :=
    hPre.trans hrun
  have h8 : evalOperand (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1)
      (.reg "%8") = some (.int 8 (hlastByte G C)) := by
    show lookupName (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1).env "%8" =
      some (.int 8 (hlastByte G C))
    simpa only [hlastByte] using hseg.inv'.iter.reg8
  exact ⟨N, hseg, by omega, h8, hcond, contWsPriceAt G C sl f hN⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scanB_ofNat
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_43
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_46
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_48
#print axioms LeanLLVM.Refinement.WalkScope.wsLandS_env
#print axioms LeanLLVM.Refinement.WalkScope.wsLandS_ee
#print axioms LeanLLVM.Refinement.WalkScope.wsLandS_cond
#print axioms LeanLLVM.Refinement.WalkScope.wsContinue43
#print axioms LeanLLVM.Refinement.WalkScope.wsContinue46
#print axioms LeanLLVM.Refinement.WalkScope.wsContinue48
#print axioms LeanLLVM.Refinement.WalkScope.wsLatchOut_facts
#print axioms LeanLLVM.Refinement.WalkScope.wsVisit43Exit
#print axioms LeanLLVM.Refinement.WalkScope.wsVisit46Exit
#print axioms LeanLLVM.Refinement.WalkScope.wsVisit48Exit
#print axioms LeanLLVM.Refinement.WalkScope.wsExit43
#print axioms LeanLLVM.Refinement.WalkScope.wsExit46
#print axioms LeanLLVM.Refinement.WalkScope.wsExit48
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_43_ee
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_43_cond
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_46_ee
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_46_cond
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_48_ee
#print axioms LeanLLVM.Refinement.WalkScope.wsLeafS_48_cond
#print axioms LeanLLVM.Refinement.WalkScope.wsRun_go
#print axioms LeanLLVM.Refinement.WalkScope.wsRun
#print axioms LeanLLVM.Refinement.WalkScope.contScanRounds
#print axioms LeanLLVM.Refinement.WalkScope.contWsEntry_ee
#print axioms LeanLLVM.Refinement.WalkScope.seamS_env_inc
#print axioms LeanLLVM.Refinement.WalkScope.seamS_env_nep
#print axioms LeanLLVM.Refinement.WalkScope.contWsSeamS_inc
#print axioms LeanLLVM.Refinement.WalkScope.contWsSeamS_nep
#print axioms LeanLLVM.Refinement.WalkScope.wsSeamSeg
#print axioms LeanLLVM.Refinement.WalkScope.wsFirstSeg43
#print axioms LeanLLVM.Refinement.WalkScope.wsFirstSeg46
#print axioms LeanLLVM.Refinement.WalkScope.wsFirstSeg48
#print axioms LeanLLVM.Refinement.WalkScope.wsEntry33
#print axioms LeanLLVM.Refinement.WalkScope.wsEntry35
#print axioms LeanLLVM.Refinement.WalkScope.wsEntry37
#print axioms LeanLLVM.Refinement.WalkScope.wsStopAt_pre43
#print axioms LeanLLVM.Refinement.WalkScope.wsStopAt_pre46
#print axioms LeanLLVM.Refinement.WalkScope.wsStopAt_pre48
#print axioms LeanLLVM.Refinement.WalkScope.contWsAfterPreAt
#print axioms LeanLLVM.Refinement.WalkScope.wsPrice
#print axioms LeanLLVM.Refinement.WalkScope.contWsRunAt33
#print axioms LeanLLVM.Refinement.WalkScope.contWsRunAt35
#print axioms LeanLLVM.Refinement.WalkScope.contWsRunAt37
#print axioms LeanLLVM.Refinement.WalkScope.wsP41Out_contLandS
#print axioms LeanLLVM.Refinement.WalkScope.wsPreSAt_transport
#print axioms LeanLLVM.Refinement.WalkScope.wsSlAt_transport
#print axioms LeanLLVM.Refinement.WalkScope.wsP41Out_35
#print axioms LeanLLVM.Refinement.WalkScope.wsPreSAt_cond
#print axioms LeanLLVM.Refinement.WalkScope.wsPreSAt_idx
#print axioms LeanLLVM.Refinement.WalkScope.wsPreSAt_envEnd
#print axioms LeanLLVM.Refinement.WalkScope.wsSlAt_envEnd
#print axioms LeanLLVM.Refinement.WalkScope.wsSlAt_env8
#print axioms LeanLLVM.Refinement.WalkScope.wsBit45
#print axioms LeanLLVM.Refinement.WalkScope.wsSlS_envEnd
#print axioms LeanLLVM.Refinement.WalkScope.contWsSeamS_env8
#print axioms LeanLLVM.Refinement.WalkScope.wsEntryAt33
#print axioms LeanLLVM.Refinement.WalkScope.wsEntryAt35
#print axioms LeanLLVM.Refinement.WalkScope.wsEntryAt37
#print axioms LeanLLVM.Refinement.WalkScope.contWsRunBody
#print axioms LeanLLVM.Refinement.WalkScope.contWsRunF
#print axioms LeanLLVM.Refinement.WalkScope.contWsPriceAt
#print axioms LeanLLVM.Refinement.WalkScope.contLandS_idx
#print axioms LeanLLVM.Refinement.WalkScope.contLandS_cond
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunFacts_of_contFacts

end WalkScope
end LeanLLVM.Refinement
