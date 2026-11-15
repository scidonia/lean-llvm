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
`walkScanRounds457`'s **round**, not at that lemma: its conclusion keeps only the counter
at the target (`%q.0.i246 = c - 1`), and the exit test reads the bound (`%cond350.i = c`)
as well, so the traversal's own aggregation cannot reach the exit.  `contScanRounds` is
that aggregation with both registers kept; its measure, its price and its induction are
`walkScanRounds457`'s, and it consumes the same three hypotheses (`hround`, `hguard`,
`hbyte`), unweakened.

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
* the scan's traversal hypotheses (`hround`, `hguard`, `hbyte`) — `walkScanRounds457`'s
  own, unweakened: the round at a byte, the latch's guard, and the input's totality at
  every index the scan visits (the model branches on a byte it does not store);
* **the token record's register at the scan's exit** (`htok`).  `if.end473.i`'s lifetime
  marker reads `%t352.i` and no block on the scan's path rebinds it, but
  `walkScanRounds457` returns its final state *existentially*, so no named term is
  available to state the cell at, and the layer has no lemma that the extra-token scan
  preserves a register.  It is stated over the states the traversal's counters pin, which
  is the closest a length-position predicate can come to the cell.  **The lemma that would
  close it is *the extra-token scan preserves a register it does not bind***; that
  statement needs the visit's target state, which the traversal's conclusion does not
  expose — the same shape as `happ₂`'s supplied record, one level out.

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
* `WalkContinueFacts` is a **class, not a `Sum`**: `HcontCase`
  (`JsonStage2WalkDispatchWitnessString`) has `ws` (`HcontFacts`), `cleanup`
  (`HcontCleanupFacts`) and `twoEntry` (`HstringFacts`, the standalone string whose merge
  index is `C.k + 2`), and the consumer splits once.  An inductive rather than a nested
  `Sum` because a `Sum` of three would re-shape every consumer twice, and the class
  question is still asked once, where the class is known.  A conditional inside a
  `Type`-valued structure would make every field a question.

**The run's refinement, landed as far as `contWsRun` is.**  The whitespace arm's seam is not
class-indexed: the run stops at the first whitespace byte, so its last visit leaves through
`LeafBlock43`, `46` or `48`, whose states differ in the cells each bounded.  So the endpoint
is **data**:

* `sl : State` and `hRun : WalkSegment … (contLandS … b35) (ContAC₄ C) (contWsSeamS C sl k b8)
  (ContSeamC C) n`, with the target carry **named** — `WalkSegment` records its target's
  invariant, so the span's first link reads `inv'` rather than a premise.  The run class's
  states are landed and so is `contWsEntry_ee`; **`contWsRun` is not**, so the run and its
  own seam step enter the bundle as one supplied segment.  Its docstring names the
  producer and its cost: five links a continuing byte and four at the exit, the per-index
  document `∀` as the traversal's premise.
* `hopS` is **produced** (`contWsEntry_hopS`: the seam stores `ofNat 64 k`, and the scan's
  phi selects `%ee.1.i` on `if.then447.i`'s edge), so the bundle carries no landing index
  and the contradiction with `heicd` is gone.
* The class survives in the run's own field: which of the three leaves `sl` came from is
  the run's business, not a bundle field, because the run is a segment whose endpoint the
  bundle already names.  The exit set `{43, 46, 48}` is the complement of the entry leaves
  `{33, 35, 37}`, and that complement check is what caught an arm list's error in a draft.
* `contWsRun`'s shape is settled: the endpoint is an **input** (a `∨` conclusion cannot fill
  a `Type` field), `≤ 5` per visit — three dispatch links plus the latch's own step — exit
  at `k`, with the per-index document group as the traversal's premise in the form `hbyte`
  already has.

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
fields.  The run's *bound* is not a clause of the invariant, which is why it stays one. -/
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

/-- The document's byte at `p`: the byte every visit of the whitespace skip loads. -/
def wsByte {m0 : Mem} (G : WalkGeom m0) (p : Nat) : UInt8 := G.bs.getD p 0

/-- The byte's register value, as `land.rhs.i` binds `%36`. -/
def wsX {m0 : Mem} (G : WalkGeom m0) (p : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (wsByte G p).toNat

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

**The run is supplied, and named as the supply.**  `hRun` is the skip's segment from the
whitespace check's target to the seam's entry, at the run class's two carries.  Its producer
is `contWsRun`: the latch's own step plus the dispatch and the leaf, which is four links a
continuing byte at `LeafBlock43`'s class and five at `46`/`48`'s, and four or five at the
exit — the landed per-visit lemmas are this module's `wsContinue43`/`46`/`48` and
`wsExit43`/`46`/`48` — with each visit's `WalkLocal` rebuilt from the document's byte and
its class, the per-index `∀` the whitespace class carries.

**Why it is a field and not yet a theorem, stated precisely.**  The per-visit pieces exist
(`walkWhiteScanVisitSeg3_43`, `walkWhiteScanVisitSeg4_46`, `walkWhiteScanVisitSeg4_48`,
`scanLatch_visit_at`), and with the latch's own step and the leaf's exit arm they are this
module's `wsContinue43`/`46`/`48` (four or five links) and `wsExit43`/`46`/`48` (four or
five, at `wsStopS`), and the entry segments and the seam are `WalkLink` applications.  What
is missing is a *term* for the endpoint: the skip's last visit leaves through one of
`LeafBlock43`, `46`, `48`, whose states differ in the cells each leaf bounded, and a segment is
stitched at its states — so `sl` cannot be an arbitrary state, and the run's recursion has to
carry the class of each index.  That is a `def` computed from the document (`wsLeafIn`,
`wsVisit`, `wsNext`, `wsRunE` in the shape the `scanT*`/`scanPreT*` states have) plus an
induction on `k - i` whose step is the three-class branch, not a missing lemma.  Its count is
`4 + 5·(k - i) + 4 + 1 = 5·(k - i) + 9`, at `i = %idxprom.i`'s value, and the field's own price
`n + 8·(v - 1 - k) ≤ 8·ΔA + 5` follows from `8ΔA ≥ 8(v - i) = 8(v - 1 - k) + 8(k - i) + 8`:
the left side is short of the right by `3·(k - i) + 4`.  **The `+9`'s exit term is `4`, which
is `LeafBlock43`'s exit;** `wsExit46` and `wsExit48` are five links (`LeafBlock46`'s test is
`eq %36, 13` and `LeafBlock48`'s `eq %36, 32`, so `13` and `32` stop the skip one link later),
so the bound's exit term has to name the class it covers.  **The price needs one premise the bundle
does not yet state:** `entryPos C.k ≤ i` for the run's start (`hstart` is about the *stop* `k`),
which is the entry stream's own fact about `%idxprom.i`, in the same supply as `hspan`/`hstart`;
and the traversal's `ScanEntered`/`ScanCount` facts need `v - i ≤ C.inner`, the entry's inner
budget, which no clause of `WalkInv` fixes at the run's start — the same supply as `hTail`'s.

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

**One cell at the run's endpoint is a field and two are not.**  `%inc.i` and `%nep` are
`WalkInv`'s own — `inc_reg` and one of `walkStaticRegs`' rows — and the seam binds neither, so
the segment's target invariant reads them at the endpoint (`contWsSeamS_inc`,
`contWsSeamS_nep`).  `%cond350.i` is not a clause of the invariant: it is bound once at
`cond.end349.i` and no block of the skip rebinds it, but a `WalkSegment` records a run and its
target's invariant rather than the blocks the run passed, so `hcond_sl` stays a field.  The
lemma that would close it is *the whitespace skip preserves the bound it does not bind* — the
`htok` gap's twin, one segment out. -/
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
  `%cond350.i - 1` and the document supplies the byte.  Its *class* is not a field: on this
  arm the three pivots' arms and the run they enter are what `hRun` carries. -/
  b35 : UInt8
  hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  /-- **The whitespace skip's endpoint, its stop and its count.**  `sl` is the state at
  `if.end372.i`'s entry that the run's last leaf reaches, `k` the run's stop (which the
  token-end `phi` selects), and `hRun` the segment from the whitespace check's target to
  the seam's entry at the run class's carries.

  **Supplied, with its producer named:** `contWsRun`, whose per-visit lemmas are landed
  (`wsContinue43`/`46`/`48`, four or five links a continuing byte by class, and
  `wsExit43`/`46`/`48`, four or five).  Its count is a **bound**, not an equality — the
  classes differ in cost, so the producer states `∃ n, n ≤ 5·(k - i) + 9 ∧ WalkSegment … n`.
  `hnRun` is the price this bundle states for that run, not a count of it. -/
  sl : State
  k : Nat
  n : Nat
  b8 : BitVec 8
  hRun : WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C)
    (contLandS C s x inc nep ep v ix b35) (ContSeamC C) (contWsSeamS C sl k b8) n
  hnRun : n + stage2ByteAllowance * (v.toNat - 1 - k) ≤
    stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5
  /-- The run's stop is inside the entry, which is what makes the extra-token span
  `[k, v.toNat)` non-empty.  **This is the field the other class cannot carry**: on the
  scan-free arm the token's end is the entry's end, so `k` would be `v.toNat`. -/
  heicd : k < v.toNat
  /-- The entry's first byte's class, read at the seam's name. -/
  x1 : BitVec 8
  h8c : evalOperand (contWsSeamS C sl k b8) (.reg "%8") = some (.int 8 x1)
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
    (contWsTailStart C sl k b8 x1)
    (TailCarryScan (ContTailStartC C) ev)
    (contWsEntry C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA) 3
  /-- The scan's landing: the byte's address and the byte.  The index is `k` — the seam's
  stored end — everywhere the landing's states name it. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName (contWsEntry C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA).env
    "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (contWsEntry C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
    (landRhs457OutAt (contWsEntry C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (contWsEntry C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q)
    (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
    (ScanS₉₆ (contWsEntry C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (contWsLatch C sl k b8 x1 r₁ r₂ r₃ k v cA rdv xA
      (BitVec.ofNat 64 k) a q x47)
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and the run's stop at or after this one's — the two facts that make
  the visits and the run no more than the span, and the price's byte term. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ k
  /-- **The run's bound at the run's endpoint, and the one cell the invariant does not
  carry.**  `%cond350.i` is `cond.end349.i`'s cell, and no block of the whitespace check or
  the skip rebinds it, but a `WalkSegment` does not name the blocks it passed — so the cell
  at `sl` is followed rather than peeled, and it is the `htok` gap's shape one segment out.

  **The run's two registers are not beside it.**  `%inc.i` is `WalkInv.inc_reg` and `%nep` is
  one of `walkStaticRegs`' pairs, and the seam binds neither, so the segment's *target*
  invariant reads both at `sl` (`contWsSeamS_inc`, `contWsSeamS_nep`). -/
  hcond_sl : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  /-- **The traversal's round**: `walkScanRounds457`'s `hround`, unweakened — a visit at
  the byte the landing loads, at the counter's own index and the lane's bound. -/
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
  /-- **The latch's guard**: `walkScanRounds457`'s `hguard`, unweakened. -/
  hguard : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ScanGuard s' "%q.0.i246" "%cond350.i" C'.inner
  /-- **The input's totality at every index the scan visits**: `walkScanRounds457`'s
  `hbyte`, unweakened — the model branches on a byte it does not store. -/
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
    C'.block = "while.body462.i" → p + 1 < v.toNat →
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
  traversal's counters pin, because `walkScanRounds457` returns its final state
  existentially; every block on the path binds its own cells and none rebinds `%t352.i`,
  so the fact is true of the model and the shape is the traversal's.

  **Supplied, not derived, and the reason is structural:** a traversal whose final state is
  existential has no named term to state a register at, and the layer has no preservation
  lemma for registers — the same shape as `happ₂` in `HlastFacts`, one level out.  The lemma
  that would close it is *the extra-token scan preserves a register it does not bind*: a
  `∀` over the scan's carries and states that a name outside the latch's and the landing's
  cell lists keeps its cell across a visit.  That statement needs the visit's target state,
  which `walkScanRounds457`'s conclusion does not expose, which is why the register enters
  here as the bundle's premise rather than as a theorem beside `scanExit_tok`. -/
  htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok)

/-- The scan's entry, at the bundle's own terms.  Named for the same reason
`hlastEntryF` is: the bundle's fields are the `def`s' arguments in order, so a lemma's
statement at `contWsEntryF f` is the one its field types spell out. -/
abbrev contWsEntryF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  contWsEntry C f.sl f.k f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.k f.v f.cA f.rdv f.xA

/-- The scan's latch, at the bundle's own terms. -/
abbrev contWsLatchF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  contWsLatch C f.sl f.k f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.k f.v f.cA f.rdv f.xA
    (BitVec.ofNat 64 f.k) f.a f.q f.x47

/-! ### The scan-free class's bundle

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
(`htok`).  What it keeps is the span to the tail's start (`hcontToSpan`'s inputs), the tail's
three calls on their empty arm, and the no-whitespace class of the byte before the entry's
end — the class whose seam stores the entry's own end.

**Why the price has no byte term.**  The bundle's segment is the twenty links
`hcontPrefixCleanupSeg` composes plus the merge's one; nothing in it consumes a document
byte beyond the two the whitespace check reads, so the entry allowance pays it whole:
`21 + 2 ≤ 32·Δk` at `Δk = 1`.  The whitespace class is the one whose price needs
`8·ΔA` — its scan's visits — and that is the arm `HcontFacts` describes. -/
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
  /-- **The byte before the entry's end and its class: no whitespace run.**  The three
  pivots take `NodeBlock41 → NodeBlock39 → LeafBlock35 → if.end372.i`, which is what makes
  the seam's stored end the entry's own end. -/
  b35 : UInt8
  hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1
  hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0
  /-- The seam's cells: the stored end at `%end.i`, the byte and its two literal tests. -/
  b8 : BitVec 8
  hend : lookupName (contP35S C s x inc nep ep v ix b35).env "%end.i" =
    some (.ptr (C.stage.tok + 8))
  h8end : lookupName (contP35S C s x inc nep ep v ix b35).env "%8" = some (.int 8 b8)
  hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
    evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The entry's first byte's class, read at the seam's name. -/
  x1 : BitVec 8
  h8c : evalOperand (contSeamS C s x inc nep ep v ix b35 b8) (.reg "%8") =
    some (.int 8 x1)
  hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0
  /-- The tail's three calls, its event and the seed's words: its segment on the empty arm,
  reaching `if.end473.i` with `TailCarryEnd`'s carry. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
    (contTailStart C s x inc nep ep v ix b35 b8 x1)
    (TailCarryEnd (ContTailStartC C) ev)
    (contCleanupEnd C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ cA rdv xA) 3

/-- The scan-free tail's end, at the bundle's own terms. -/
abbrev contCleanupEndF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  contCleanupEnd C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.r₁ f.r₂ f.r₃
    f.cA f.rdv f.xA

/-- The tail's start, at the bundle's own terms: the segment's source, where the body of
the merge's composition reads its cells. -/
abbrev contTailStartF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  contTailStart C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1

/-- **The scan's visits, counted with the registers kept.**  `walkScanRounds457` counts
the visits but keeps only the counter at its target; the exit test reads the bound too, so
the recursion here is at the round's own granularity (`hround`, the traversal's own
hypothesis) and its conclusion carries both registers.  The price bound is the traversal's
own: one byte allowance per visit, `cd - 1 - ei` of them.

**This is the two-register twin of `walkScanRounds457`, not a simplification of it, and it
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
    (hc63 : f.v.toNat ≤ 2 ^ 63) (hic : i < f.v.toNat) :
    ∃ (C'' : WalkCarry G) (s'' : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' n ∧ WalkInv G C'' s'' ∧
      C''.block = "while.body462.i" ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
      n ≤ stage2ByteAllowance * (f.v.toNat - 1 - i) := by
  have go : ∀ r, ∀ (i : Nat) (K : WalkCarry G) (t : State), f.v.toNat - 1 - i = r →
      WalkInv G K t → K.block = "while.body462.i" →
      ScanGuard t "%q.0.i246" "%cond350.i" K.inner →
      lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) →
      i < f.v.toNat →
      ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
        K'.block = "while.body462.i" ∧
        lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
        lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
        n ≤ stage2ByteAllowance * r := by
    intro r
    induction r with
    | zero =>
        intro i K t _ hInv hblock _ hi hb hic
        have hie : i = f.v.toNat - 1 := by omega
        exact ⟨K, t, 0, Seg.measure (Seg.nil hInv), hInv, hblock,
          by rw [← hie]; exact hi, hb, by simp⟩
    | succ r ih =>
        intro i K t hr hInv hblock hg hi hb hic
        have hlt : i + 1 < f.v.toNat := by omega
        have hpos : i + 1 < 2 ^ 63 := by omega
        obtain ⟨a, bs, q, x, h3, hread, hbs, h47, hbit, hws, hl105, hl96, hll⟩ :=
          f.hbyte K t i hInv hblock hlt hi hb
        obtain ⟨K₁, t₁, j, hseg, hInv₁, hb₁, hj, hi₁, hc₁⟩ :=
          f.hround K t i a bs q x hInv hblock hi hb hlt hpos h3 hread hbs h47 hbit hws
            hl105 hl96 hll
        obtain ⟨K₂, t₂, m, hseg₂, hInv₂, hb₂, hi₂, hc₂, hm⟩ :=
          ih (i + 1) K₁ t₁ (by omega) hInv₁ hb₁ (f.hguard K₁ t₁ hInv₁ hb₁) hi₁ hc₁
            (by omega)
        refine ⟨K₂, t₂, j + m, hseg.trans hseg₂, hInv₂, hb₂, hi₂, hc₂, ?_⟩
        rw [Nat.mul_succ]
        omega
  exact go (f.v.toNat - 1 - i) i C' s' rfl hInv hblock (f.hguard C' s' hInv hblock) hi hb hic

/-! ### The two arms' compositions, and where they are

Neither arm's composition lives here.  The whitespace arm's goes through the run
(`HcontFacts.hRun`), the seam, the class-C span, the tail and the scan's visits, and it
records the merge's three cells; the scan-free arm's is `hcontPrefixCleanupSeg` plus the
merge's step.  Both are `JsonStage2WalkRevolutionSeg`'s (`walkRevolutionMergeSegWs` and
`walkRevolutionMergeSeg`), because the cells are read at the endpoint's named state and the
traversal that carries the registers is that module's.

The composition this file used to state (`walkRevolution_seg`) is gone rather than kept
beside them: its premise was the bundle at the *scan-free* states, so it named a path the
walk does not take from a state the walk does reach — the vacuity this module's header
records.  What survives here is the bundle, and the traversal lemma (`contScanRounds`) both
arms' compositions share. -/

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
#print axioms LeanLLVM.Refinement.WalkScope.contScanRounds
#print axioms LeanLLVM.Refinement.WalkScope.contWsEntry_ee
#print axioms LeanLLVM.Refinement.WalkScope.seamS_env_inc
#print axioms LeanLLVM.Refinement.WalkScope.seamS_env_nep
#print axioms LeanLLVM.Refinement.WalkScope.contWsSeamS_inc
#print axioms LeanLLVM.Refinement.WalkScope.contWsSeamS_nep

end WalkScope
end LeanLLVM.Refinement
