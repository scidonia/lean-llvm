/-
# The continuing entry's merge cells, from the head to `cleanup478.i`

## The cells, and the premise that could not state them

`walkMergeCells_ws` and `walkMergeCells_cleanup` each supply three facts at the merge for
*every* head state with their arm's bundle, at the composition's own endpoint:

```
Cd.k = C.k
lookupName sd.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
lookupName sd.env "%nep"    = some (.int 64 (BitVec.ofNat 64 G.nep))
```

No producer for the *unrestricted* premise existed: `WalkSegment` carries a run and an
invariant, and neither names the blocks the run passed or the registers they bound, so a
segment whose endpoint is an existential witness has no term to read a cell at.  The way out
is the one
`stringPath_seg` (`JsonStage2WalkDispatchWitnessString`) takes for the two-entry arm —
**name the states and the carries**, so the endpoint is a term of the composition — and two
things the earlier revolution left existential have to be named for it:

* **the extra-token scan's round.**  `walkScanRound457` proves one visit's four steps and
  states its target as `∃ C' s' n, …`; its proof already builds the named target
  (`Latch462S (scanLatchOut …)` at `{ ScanCLand C with block := "while.body462.i" }`), and
  `scanRoundSeg4` is that proof at those names.  `scanWsRounds` is the traversal — the
  counter and the bound `contScanRounds` keeps, **plus `%inc.i`, `%nep` and the carry's
  index** — composed of rounds rather than of the bundle's `hround`.  This is the whole
  point: a round whose target is a witness has no environment, so a register cannot be
  carried across it; a round whose target is `Latch462S …` can be peeled, because the eight
  cells it binds (`%inc463.i`, `%exitcond298.not`, `%47`, `%arrayidx458.i`, `%q.0.i246`,
  `%Pivot106`, `%.off97`, `%SwitchLeaf98`) do not include `%inc.i` or `%nep`
  (`scanRoundOut_inc`/`_nep`);
* **the latch's exit and the merge.**  `scanExitSeg` and `walkIfEnd473_at` name their
  targets already — `scanLatchOut … "if.end473.i"` and `{ s with pc := "cleanup478.i", … }`
  — so `revExitS`, `revExitC`, `revMergeS` and `revMergeC` are those terms and the merge's
  environment is the exit's (`revMergeS_inc`/`_nep` are `rfl`).

## The two compositions, their counts and their endpoints

The module states **one composition per arm**, because the arms leave `if.then447.i` by
different edges and a segment is stitched at its states:

`walkRevolutionMergeSeg` — the **scan-free** arm — composes

| piece | lemma | links |
|---|---|---|
| the head, the whitespace check, the seam and the class-C span | `hcontPrefixCleanupSeg` → `hcontToSpan` | `8 + 4 + 5` |
| the tail's three calls, on their empty arm | the bundle's `hTail` (`consumerTailSegEmptyAt`'s shape) | `3` |
| the merge | `walkIfEnd473_at` | `1` |

at `20 + 1 = 21`, from the loop head `s` to `clnMergeS f` at `clnMergeC C f.ev`, with the
price `21 + 2 ≤ 32·Δk` — **no byte term**, because this arm spends no document byte after
the whitespace check's two.  Its three cells are `clnMergeC_k` (rfl), `contCleanupEndF_inc`
and `contCleanupEndF_nep`: the seam, the span and the tail rebind neither register.

`walkRevolutionMergeSegWs` — the **whitespace** arm — composes

| piece | lemma | links |
|---|---|---|
| the head path to the whitespace check | `contPrefixLand` | `8` |
| the skip and the seam | `contWsRunF` derives it from the class field | `N` |
| the class-C span | `walkHeadChainCSeg` | `5` |
| the tail's three calls | the bundle's `hTail` | `3` |
| the scan's landing | `walkScanLinks457`, `hopS` produced | `3` |
| the scan's visits, four steps each | `scanWsRounds` → `scanRoundSeg4` | `nSc`, `nSc ≤ 4·(v - 1 - k)` |
| the latch's exit | `scanExitSeg` | `1` |
| the merge | `walkIfEnd473_at` | `1` |

at `(((8 + N) + 5) + 3 + 3) + nSc + 1 + 1`, to `revMergeS sm f.v.toNat` at `revMergeC Cm`.
Its price is `p + 2 ≤ 32·Δk + 8·ΔA`, and the byte term is the arm's own: `contWsPriceF`
states that the run and the scan's *whole* span share the entry's, `N + 8·(v - 1 - k) ≤
8·ΔA + 5`, which is the budget-not-double-spent argument in one inequality — the scan's start
**is** the run's stop.

Both conclusions state the three cells **beside** the segment, at the segment's own
endpoints: the carry's index, the `%inc.i` cell and the `%nep` cell.  Nothing is quantified
over a state the run does not reach, which is what makes them readable.

**`HcontFacts.hround` is not consumed here.**  The bundle's round premise is the traversal's
per-visit step stated existentially (`∃ C'' s'', …`), and `scanWsRounds` proves each visit
from `scanRoundSeg4` instead — which is what the register cells require.  So the whitespace
composition's demands on the bundle are `hbyte` and `hguard` (and the run's, through
`contWsRunF`): `hround` is left unused rather than re-stated.

## The head state's two cells, and where they come from

Both cells are `WalkInv` clauses now, so `MergeHeadCells` is a theorem at any invariant
state (`mergeHeadCells`):

* `%inc.i = C.k + 1`: `WalkInv.inc_reg`, the header's bind (`whileBodyOut_inc` —
  `%inc.i` is `%k.0.i249 + 1`) read at `blockIndex`'s value.  The clause is uniform, not
  block-keyed: the back edge (`walkBack_step`) advances neither the carry's `C.k` nor the
  register, and the one rebind (`whileBody_step`) moves both together, so
  `%inc.i = C.k + 1` holds at every block — `while.body.i` included.  The block-keyed
  alternative (`ofNat C.k` at `while.body.i`) would demand `C.k = %k.2.i` and is refuted
  by `hkge`;
* `%nep = G.nep`: `%nep` is one of `walkStaticRegs`' pairs (`WalkInv.regs`), since the
  entry binds it and no block of the walk rebinds the name.

Neither is a field of `HcontFacts`: that bundle is the *input's* facts (the document's
bytes, the scan's landing, the traversal's hypotheses), and these two are the run's
registers.

## The `∀`-forms

Each arm has one, and each is a `∀` over head states — `WalkInv`, the loop head, an entry
left and that arm's bundle — concluding the segment, its endpoint and the three cells:

* `walkMergeCells_ws` for the whitespace arm (`HcontFacts`), whose endpoint is
  `revMergeS sm v.toNat` at `revMergeC Cm`;
* `walkMergeCells_cleanup` for the scan-free arm (`HcontCleanupFacts`), whose endpoint is
  `clnMergeS f` at `clnMergeC C f.ev`.

`walkHeadCells` is the same `∀` for the loop's step, over `MergeHeadCells`, which is a
`WalkInv` clause pair rather than a bundle.

**Which arm a bundle describes is that module's question, and these producers add no
premise to it.**  `HcontFacts` is the whitespace class (its class field decides the seam's
stored end, and `contWsRunF` derives the run from it) and `HcontCleanupFacts` is the class
whose byte before the entry's end is not whitespace; each composition reads only its own
bundle's fields, at its own states.

`walkDispatch_at_continue_cells_ws` and `walkDispatch_at_continue_cells` are the per-state
dispatch bodies for the two arms, and `walkDispatch_of_continue_cells` is the scan-free
arm's bridge to the quantified form: `WalkDispatch` follows from that bundle's `∀`-form
alone, with no fact about a segment the producer did not build.  The whitespace arm's bridge
is `walkDispatch_of_continue` (`JsonStage2WalkPremisesOfStaging`), over
`WalkContinueWsFacts`.

**This module does not import `JsonStage2WalkPremisesOfStaging`**, so that the consumers of
the continuing entry's premise — `JsonStage2WalkPremisesOfStaging` among them — can import
this one and read the producers.  The names it would take from there are written out: the
bridges' first hypotheses are the two `∀`-forms' types, and the merge's two `phiIncoming`
cells are `decide`s on `cleanupSpIncoming`/`cleanupKIncoming`.

**The unrestricted premise is not derived here, and its first conjunct is not a
consequence of the walk's invariant at an arbitrary segment.**  That premise would quantify
over every segment from a head state to `cleanup478.i`, while a `WalkSegment` carries a run
and an invariant and nothing about the blocks the run passed — so a segment that passes the
header is not excluded, and the CFG offers one: `cleanup478Block`'s term branches to
`while.body.i` when its own test passes, and `whileBodyBlock`'s term branches back to
`NodeBlock21`.  `whileBody_step` sets the carry's index to the merge's `%k.2.i` (the phi
whose incoming from `if.end473.i` is `%inc.i`), above the carried `C.k`, so on such a
segment the first conjunct is `Cd.k = C.k + 1` rather than `Cd.k = C.k`.  Whether a concrete
document makes that segment reachable is a question about the input and is not settled here;
what is settled is that the unrestricted quantification reaches past what the producer
builds, and that the producer's endpoint is the instance `walkDispatch_at_continue_cells`
reads its three cells at.
-/

import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The endpoint, named

The scan's exit and the merge, at the terms `scanExitSeg` and `walkIfEnd473_at` build.  The
merge's block is a lifetime marker and a `br`, so it binds no cell and the exit's
environment is the merge's. -/

/-- The scan's exit at its last visit: `scanExitSeg`'s own target. -/
abbrev revExitS (s : State) (c : Nat) : State :=
  scanLatchOut s "%inc463.i" "%exitcond298.not" (c - 1) c "if.end473.i"

/-- **The merge, named.**  `walkIfEnd473_at`'s target: the exit's state at the merge, the
lifetime marker writing nothing. -/
abbrev revMergeS (s : State) (c : Nat) : State :=
  { revExitS s c with pc := "cleanup478.i", pre := some (revExitS s c).pc }

/-- The scan's exit carry. -/
abbrev revExitC {m0 : Mem} {G : WalkGeom m0} (Cm : WalkCarry G) : WalkCarry G :=
  { Cm with block := "if.end473.i" }

/-- The merge's carry. -/
abbrev revMergeC {m0 : Mem} {G : WalkGeom m0} (Cm : WalkCarry G) : WalkCarry G :=
  { revExitC Cm with block := "cleanup478.i" }

/-! ### The cells the two links do not bind

The exit binds `%inc463.i` and `%exitcond298.not`; the merge binds nothing.  So `%inc.i` and
`%nep` are the scan's own cells at the exit and the merge. -/

/-- `%inc.i` at the scan's exit is the latch's. -/
theorem revExitS_inc (s : State) (c : Nat) :
    lookupName (revExitS s c).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [revExitS, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the scan's exit is the latch's. -/
theorem revExitS_nep (s : State) (c : Nat) :
    lookupName (revExitS s c).env "%nep" = lookupName s.env "%nep" := by
  simp only [revExitS, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%inc.i` at the merge is the exit's: the merge's block binds no cell. -/
theorem revMergeS_inc (s : State) (c : Nat) :
    lookupName (revMergeS s c).env "%inc.i" = lookupName (revExitS s c).env "%inc.i" := rfl

/-- `%nep` at the merge is the exit's. -/
theorem revMergeS_nep (s : State) (c : Nat) :
    lookupName (revMergeS s c).env "%nep" = lookupName (revExitS s c).env "%nep" := rfl

/-- The merge's carry keeps the scan's index: `revMergeC` updates the block twice. -/
theorem revMergeC_k {m0 : Mem} {G : WalkGeom m0} (Cm : WalkCarry G) :
    (revMergeC Cm).k = Cm.k := rfl

/-! ### The scan-free arm's endpoint, named

The merge is `walkIfEnd473_at`'s target at the tail's empty end: `if.end473.i`'s lifetime
marker writes no cell, so the merge's environment is the tail's end's and the merge's
predecessor is that end's block.  The carry advances from `TailCarryEnd` by one block
update, and its index is the head state's — nothing in the tail rebinds `%k.0.i249`.

The endpoint is a term of the composition rather than a witness, which is what lets the
three cells be read at it: `%inc.i` and `%nep` are peeled through the seam, the class-C
span and the tail's three calls, none of which binds either. -/

/-- The merge's carry, from the scan-free tail's: one block update on `TailCarryEnd`. -/
abbrev clnMergeC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { TailCarryEnd (ContTailStartC C) ev with block := "cleanup478.i" }

/-- The merge, named, on the scan-free arm: `walkIfEnd473_at`'s target at the tail's end. -/
def clnMergeS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  { contCleanupEndF f with pc := "cleanup478.i", pre := some "if.end473.i" }

/-- The merge's carry keeps the head state's index. -/
theorem clnMergeC_k {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (clnMergeC C ev).k = C.k := rfl

/-- `%inc.i` at the scan-free tail's end is the loop head's: the seam binds `%ee.1.i`,
`%end.i` and the byte's cells, the class-C span its own five, and the tail's three calls
`%kind404.i`, `%38`, `%call416.i`, `%tobool417.not.i`, `%.sink372`, `%call427.i`,
`%tobool428.not.i` and `%cmp451.i` — none of them is the header's increment. -/
theorem contCleanupEndF_inc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) :
    lookupName (contCleanupEndF f).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [contCleanupEndF, contCleanupEnd, ScanEntry, TailS₃, TailS₂, TailS₁,
    contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS, seamFin,
    contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt, condEnd349OutAt,
    contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the scan-free tail's end is the loop head's, for the same reason. -/
theorem contCleanupEndF_nep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) :
    lookupName (contCleanupEndF f).env "%nep" = lookupName s.env "%nep" := by
  simp only [contCleanupEndF, contCleanupEnd, ScanEntry, TailS₃, TailS₂, TailS₁,
    contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS, seamFin,
    contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt, condEnd349OutAt,
    contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **The token record at the scan-free tail's end**, which is what the merge's lifetime
marker reads.  No block on this path rebinds `%t352.i`, so the cell is the head state's. -/
theorem contCleanupEndF_tok {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) :
    lookupName (contCleanupEndF f).env "%t352.i" = some (.ptr C.stage.tok) := by
  have hS : lookupName s.env "%t352.i" = some (.ptr C.stage.tok) :=
    (headAS5_envTokEq s f.x f.inc f.nep).symm.trans
      (show lookupName (headAS₅ s f.x f.inc f.nep).env "%t352.i" =
        some (.ptr C.stage.tok) from f.htok5)
  simp only [contCleanupEndF, contCleanupEnd, ScanEntry, TailS₃, TailS₂, TailS₁,
    contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS, seamFin,
    contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt, condEnd349OutAt,
    contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hS


/-! ### The round, named

`walkScanRound457` proves one visit's four steps — the latch's own increment and test, the
landing's three links — and states its target as a witness of an existential.  Its proof
already builds the named target (`Latch462S (scanLatchOut …)` at the carry
`{ ScanCLand C with block := "while.body462.i" }`), so this is the same four steps at those
names: the traversal below composes rounds, and a round it cannot name is a register it
cannot carry.

The cells the round binds are `%inc463.i`, `%exitcond298.not`, `%47`, `%arrayidx458.i`,
`%q.0.i246`, `%Pivot106`, `%.off97` and `%SwitchLeaf98`; `%inc.i` and `%nep` are not among
them, which is what `scanRoundOut_inc`/`_nep` say. -/

/-- `%inc.i` at a round's target is its source's: none of the eight cells the round binds
is `%inc.i`. -/
theorem scanRoundOut_inc (s : State) (i c : Nat) (idx : BitVec 64) (a q : Nat)
    (x : BitVec 8) :
    lookupName (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" i c
      "land.rhs457.i") idx a q x).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at a round's target is its source's. -/
theorem scanRoundOut_nep (s : State) (i c : Nat) (idx : BitVec 64) (a q : Nat)
    (x : BitVec 8) :
    lookupName (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" i c
      "land.rhs457.i") idx a q x).env "%nep" = lookupName s.env "%nep" := by
  simp only [Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **One visit of the extra-token scan, its target named.**  Four steps: the latch's
`%inc463.i` and its equality test, then `land.rhs457.i`'s three links.  The target is
`Latch462S (scanLatchOut …) (ofNat 64 (i + 1)) a q x` at the carry
`{ ScanCLand C with block := "while.body462.i" }` — the term `walkScanRound457`'s proof
builds and does not state. -/
theorem scanRoundSeg4 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body462.i")
    {i c : Nat} (hi : lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hlt : i + 1 < c) (hposi : i + 1 < 2 ^ 63)
    (hinner : c - (i + 1) ≤ C.inner)
    {a : Nat} {bs : List UInt8} {q : Nat} {x : BitVec 8}
    (h3 : lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i").env
      "%3" = some (.ptr a))
    (hread : readBytes s.mem (a + (i + 1)) 1 = some bs)
    (hbs : bytesToNat bs = q)
    (hloc105 : WalkLocal (ScanC₁₀₅ (ScanCLand C))
      (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i")
        (BitVec.ofNat 64 (i + 1)) a q))
    (h47 : evalOperand (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" i c
      "land.rhs457.i") (BitVec.ofNat 64 (i + 1)) a q) (.reg "%47") = some (.int 8 x))
    (hbit : evalICmp .slt x (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hloc96 : WalkLocal (ScanC₉₆ (ScanCLand C))
      (ScanS₉₆ (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i")
        (BitVec.ofNat 64 (i + 1)) a q x))
    (hlatch : WalkLocal { ScanCLand C with block := "while.body462.i" }
      (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i")
        (BitVec.ofNat 64 (i + 1)) a q x)) :
    WalkSegment calls G C s { ScanCLand C with block := "while.body462.i" }
      (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i")
        (BitVec.ofNat 64 (i + 1)) a q x) 4 := by
  have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : ((BitVec.ofNat 64 (i + 1)).signExtend 64).toNat
      = (BitVec.ofNat 64 (i + 1)).toNat := by
    simp [BitVec.signExtend]
  have hpre : (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i").pre
      = some "while.body462.i" := by
    dsimp only [scanLatchOut, stateAt, State.bind]
    rw [hInv.pc_eq, hblock]
  have hincCell : lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c
      "land.rhs457.i").env "%inc463.i" = some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
    dsimp only [scanLatchOut, stateAt, State.bind, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcondCell : lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c
      "land.rhs457.i").env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
    dsimp only [scanLatchOut, stateAt, State.bind, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hc
  have hexit : WalkLocal { C with block := "if.end473.i" }
      (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "if.end473.i") := by
    simp [WalkLocal]
  have hland : WalkLocal { C with block := "land.rhs457.i" }
      (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i") := by
    rw [WalkLocal.extraTokenLanded rfl]
    exact Or.inl ⟨i + 1, c, hinner, hlt, hcw, hpre, hincCell, hcondCell⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, -, -, -⟩ :=
    scanLatch_visit_at (calls := calls) (G := G) (C := C) (s := s) hInv hblock
      (src := "while.body462.i") (inc := "%inc463.i") (phi := "%q.0.i246")
      (test := "%exitcond298.not") (cond := "%cond350.i") (exit := "if.end473.i")
      (land := "land.rhs457.i")
      (B := scanBlock "while.body462.i" "%inc463.i" "%q.0.i246" "%exitcond298.not"
        "%cond350.i" "if.end473.i" "land.rhs457.i")
      scanExtraToken_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt hexit hland
  rw [hC₁] at hseg₁
  rw [hs₁] at hseg₁
  obtain ⟨s₃, hs₃, hseg₃⟩ := walkScanLinks457 (calls := calls) (G := G) (C := ScanCLand C)
    (s := scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i")
    hseg₁.inv' rfl hpre
    (sel := Operand.reg "%inc463.i") (by decide)
    (by
      dsimp only [scanLatchOut, stateAt, State.bind, cells]
      simp only [evalOperand]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
    (x := x) (a := a) (q := q) (bs := bs) h3
    (by rw [h2, h1]; omega)
    (by
      have hr : readBytes s.mem (a + ((BitVec.ofNat 64 (i + 1)).signExtend 64).toNat) 1
          = some bs := by rw [h2, h1]; exact hread
      simpa only [scanLatchOut, stateAt, State.bind] using hr)
    hbs hloc105 h47 hbit hws hloc96 hlatch
  rw [hs₃] at hseg₃
  exact hseg₁.trans hseg₃

/-! ### The scan's visits, with the registers carried

`contScanRounds` (`JsonStage2WalkRevolution`) counts the same visits and keeps the two
registers the exit reads.  This is that traversal with three more cells in the conclusion —
`%inc.i`, `%nep` and the carry's index — because the merge reads them, and it composes
`scanRoundSeg4` rather than the bundle's `hround`: a round whose target is a witness has no
environment to read a cell at, which is exactly why the merge's cells had no producer.

The price is `4` per visit, not the byte allowance's `8`: the round's four steps are the
latch's own and the dispatch's three links, and `walkScanRound457`'s bound was never tight.
-/

/-- **The extra-token scan's visits, at the merge's registers.**  From a latch state whose
counter is `i` and whose bound is the lane's word to the latch state at the last visit
(`v - 1`), carrying `%inc.i`, `%nep` and the carry's index unchanged across the visits —
none of the eight cells a round binds is one of them, and the round's carries change the
block and the inner budget only. -/
theorem scanWsRounds {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s) {K : WalkCarry G} {t : State} {i : Nat} {inc0 nep0 : BitVec 64}
    {k0 : Nat} (hInv : WalkInv G K t) (hblock : K.block = "while.body462.i")
    (hi : lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hb : lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)))
    (hinc : lookupName t.env "%inc.i" = some (.int 64 inc0))
    (hnep : lookupName t.env "%nep" = some (.int 64 nep0))
    (hk : K.k = k0) (hic : i < f.v.toNat) :
    ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
      K'.block = "while.body462.i" ∧ K'.k = k0 ∧
      lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
      lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
      lookupName t'.env "%inc.i" = some (.int 64 inc0) ∧
      lookupName t'.env "%nep" = some (.int 64 nep0) ∧
      n ≤ 4 * (f.v.toNat - 1 - i) := by
  have hc64 : f.v.toNat < 2 ^ 64 := by have := f.v.isLt; omega
  have go : ∀ r, ∀ (i : Nat) (K : WalkCarry G) (t : State) (inc0 nep0 : BitVec 64)
      (k0 : Nat), f.v.toNat - 1 - i = r →
      WalkInv G K t → K.block = "while.body462.i" →
      lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) →
      lookupName t.env "%inc.i" = some (.int 64 inc0) →
      lookupName t.env "%nep" = some (.int 64 nep0) →
      K.k = k0 → i < f.v.toNat →
      ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
        K'.block = "while.body462.i" ∧ K'.k = k0 ∧
        lookupName t'.env "%q.0.i246" =
          some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
        lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
        lookupName t'.env "%inc.i" = some (.int 64 inc0) ∧
        lookupName t'.env "%nep" = some (.int 64 nep0) ∧
        n ≤ 4 * r := by
    intro r
    induction r with
    | zero =>
        intro i K t inc0 nep0 k0 hr hInv hblock hi hb hinc hnep hk hic
        have hie : i = f.v.toNat - 1 := by omega
        exact ⟨K, t, 0, Seg.measure (Seg.nil hInv), hInv, hblock, hk,
          by rw [← hie]; exact hi, hb, hinc, hnep, by simp⟩
    | succ r ih =>
        intro i K t inc0 nep0 k0 hr hInv hblock hi hb hinc hnep hk hic
        have hlt : i + 1 < f.v.toNat := by omega
        obtain ⟨a, bs, q, x, h3, hread, hbs, h47, hbit, hws, hl105, hl96, hll⟩ :=
          f.hbyte K t i hInv hblock hlt hi hb
        have hSC : ScanCount t "%q.0.i246" "%cond350.i" K.inner := by
          have h := hInv.blockLocal
          rwa [WalkLocal.extraToken hblock] at h
        have hinner : f.v.toNat - i ≤ K.inner := ScanCount.same hSC hi hb hc64 hic
        have hinner' : f.v.toNat - (i + 1) ≤ K.inner := by omega
        have hposi : i + 1 < 2 ^ 63 := by have := f.v.isLt; omega
        have hseg : WalkSegment (stage2Calls stage2SubCalls) G K t
            { ScanCLand K with block := "while.body462.i" }
            (Latch462S (scanLatchOut t "%inc463.i" "%exitcond298.not" i f.v.toNat
              "land.rhs457.i") (BitVec.ofNat 64 (i + 1)) a q x) 4 :=
          scanRoundSeg4 (calls := stage2Calls stage2SubCalls) G K t hInv hblock hi hb hc64
            hlt hposi hinner' h3 hread hbs hl105 h47 hbit hws hl96 hll
        obtain ⟨K₂, t₂, m, hseg₂, hInv₂, hb₂, hk₂, hi₂, hc₂, hinc₂, hnep₂, hm⟩ :=
          ih (i + 1) { ScanCLand K with block := "while.body462.i" }
            (Latch462S (scanLatchOut t "%inc463.i" "%exitcond298.not" i f.v.toNat
              "land.rhs457.i") (BitVec.ofNat 64 (i + 1)) a q x) inc0 nep0 k0
            (by omega) hseg.inv' rfl
            (latch462S_counter (m0 := m0) t i f.v.toNat (BitVec.ofNat 64 (i + 1)) a q x)
            (latch462S_cond (m0 := m0) t i f.v.toNat (BitVec.ofNat 64 (i + 1)) a q x hb)
            (by rw [scanRoundOut_inc]; exact hinc)
            (by rw [scanRoundOut_nep]; exact hnep)
            hk (by omega)
        refine ⟨K₂, t₂, 4 + m, hseg.trans hseg₂, hInv₂, hb₂, hk₂, hi₂, hc₂, hinc₂, hnep₂, ?_⟩
        rw [Nat.mul_succ]
        omega
  exact go (f.v.toNat - 1 - i) i K t inc0 nep0 k0 rfl hInv hblock hi hb hinc hnep hk hic

/-! ### The head state's two cells, and their producers

**`WalkInv` carries both, and `MergeHeadCells` is the name of the pair:**

* `%inc.i = C.k + 1` is `WalkInv.inc_reg` — the header's bind, `whileBodyOut_inc`, read at
  `blockIndex`'s value.  The clause is uniform rather than block-keyed, so the back edge and
  the header's pass both keep it;
* `%nep = G.nep` is one of `walkStaticRegs`' rows, read through `WalkInv.regs`: the entry
  binds it (`walkEntryNep`) and no block of the walk rebinds it.

So neither is a field of `HcontFacts`, whose group is the *input's* facts — the document's
bytes and the scan's landing — and the pair is produced from the invariant (`mergeHeadCells`)
rather than supplied. -/

/-- The header's own `%inc.i` cell: the register is `%k.0.i249 + 1`, which is what makes the
loop head's value `C.k + 1` once `blockIndex` fixes the phi. -/
theorem whileBodyOut_inc {env : Env} {k sp b ep c q : Nat} {bt : UInt8} :
    lookupName (whileBodyOut env k sp b ep c q bt) "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
  simp [whileBodyOut, cells, lookupName]

/-- `%nep`'s cell at the entry state the staging builds: the argument, not a word the walk
writes. -/
theorem walkEntryNep {b n ep nep xp nxp dst dstcap ndst ev evcap nev err d c ctype cst tok s
    z e : Nat} {mem : Mem} {next : Nat} :
    lookupName (EntryState stage2Body
      (stage2Args [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
        .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
        .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
        .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] d c ctype cst tok s z e)
      mem next).env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)) := by
  rw [walkEntryState_env]
  rfl

/-- The head state's two register cells, as one shape: `mergeHeadCells` produces it from
`WalkInv` alone. -/
structure MergeHeadCells {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop where
  /-- The header's increment, at the carried index. -/
  hinc : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
  /-- The stream's count, which the walk never rebinds. -/
  hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))

/-- **The merge's two cells are the invariant's.**  `WalkInv.inc_reg` is the
header's increment at the carried index, and `%nep` is one of `walkStaticRegs`'
pairs (`WalkInv.regs`), so neither is a premise any more.  `inc_reg`'s uniform
form is what makes this a field read rather than a case on `C.block`: the back
edge carries `k` unadvanced and `%inc.i` still `C.k + 1`, and the header's pass
moves both together. -/
theorem mergeHeadCells {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) : MergeHeadCells G C s :=
  ⟨hInv.inc_reg, hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
    (by simp [walkStaticRegs])⟩

/-- **The merge's cells at every head state with an entry left.**  The `∀`-form the
loop's step and `WalkDispatch`'s bridge read, produced from the invariant alone. -/
theorem walkHeadCells {m0 : Mem} (G : WalkGeom m0) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → MergeHeadCells G C s :=
  fun _ _ hInv _ _ => mergeHeadCells hInv

/-- `%inc.i` at the whitespace arm's latch is the run's endpoint's: the seam binds
`%ee.1.i`, `%end.i` and the byte's cells, the class-C span its own five, the tail's three
calls theirs, and the scan's landing and latch the lattice's eight — none of them is the
header's increment. -/
theorem contWsLatch_inc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) :
    lookupName (contWsLatchF f).env "%inc.i" =
      lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env "%inc.i" := by
  simp only [contWsLatchF, contWsLatch, Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut,
    contWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contWsTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the whitespace arm's latch is the run's endpoint's, for the same reason. -/
theorem contWsLatch_nep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) :
    lookupName (contWsLatchF f).env "%nep" =
      lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env "%nep" := by
  simp only [contWsLatchF, contWsLatch, Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut,
    contWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contWsTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the whitespace arm's latch is the lane's word: the seam, the span, the
tail, the landing and the latch rebind names, but none of them rebinds the scan's bound, so
the cell the run's producer returns at its endpoint is the latch's. -/
theorem contWsLatch_cond {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s)
    (hcond : lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat))) :
    lookupName (contWsLatchF f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := by
  simp only [contWsLatchF, contWsLatch, Latch462S, ScanS₉₆, landRhs457OutAt, scanLatchOut,
    contWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contWsTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hcond

/-- The scan's entry's predecessor on the whitespace arm is the copy call's block: the
seam's stored end travels through the span and the tail's three calls, none of which
rebinds the predecessor cell. -/
theorem contWsEntry_pre {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) :
    (contWsEntryF f).pre = some "if.then447.i" := by
  simp only [contWsEntryF, contWsEntry, ScanEntry, TailS₃, TailS₂]

/-- **`hopS` is produced on the whitespace arm.**  The scan's entry `phi` selects
`%ee.1.i` on `if.then447.i`'s edge (`hlastEntry_phiSel`), and the seam stored the run's
stop `k` in that cell (`contWsEntry_ee`), so the landing's index *is* the run's stop.  This
is the field the bundle used to carry and the one whose assertion made it uninhabited at
the other class's states: there `%ee.1.i` was `%cond350.i`, i.e. `v.toNat`. -/
theorem contWsEntry_hopS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) :
    evalOperand (stateAt (contWsEntryF f).env (contWsEntryF f)) (.reg "%ee.1.i") =
      some (.int 64 (BitVec.ofNat 64 f.k)) := by
  simp only [evalOperand, stateAt]
  exact contWsEntry_ee C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1 f.x1
    f.r₁ f.r₂ f.r₃ f.k f.v f.cA f.rdv f.xA

/-! ### The composition

The head path at its twenty-three, the scan's visits at four each, the latch's exit and the
merge: the endpoint is `revMergeS sm v` and the last three conjuncts are the merge's three
cells read at it. -/

/-- **The scan-free arm's path to the merge, with the merge's cells at its endpoint.**
`hcontPrefixCleanupSeg`'s twenty links and the merge's own step, at the endpoint
`clnMergeS f` and the carry `clnMergeC C f.ev` — both terms of the composition, so the three
cells are read where the run actually ends.

The price is the entry's own: `21 + 2 ≤ 32·Δk` at `Δk = 1`, and **no byte term** — this arm
spends no document byte after the whitespace check's two, so the visits a scan would charge
for do not exist here.  That is the difference the last-entry repair turned on, carried to
the continuing arm: the token's end is the entry's end, `if.then447.i`'s test is `ult v v`,
and the merge is reached without entering the scan. -/
theorem walkRevolutionMergeSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (clnMergeC C f.ev) (clnMergeS f) 21 ∧
      WalkInv G (clnMergeC C f.ev) (clnMergeS f) ∧
      (clnMergeC C f.ev).block = "cleanup478.i" ∧
      (clnMergeS f).pre = some "if.end473.i" ∧
      (clnMergeC C f.ev).k = C.k ∧
      lookupName (clnMergeS f).env "%inc.i" =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName (clnMergeS f).env "%nep" =
        some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      21 + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) := by
  -- the span and the scan-free tail: twenty links to the merge's entry
  have hsegP : WalkSegment (stage2Calls stage2SubCalls) G C s
      (TailCarryEnd (ContTailStartC C) f.ev) (contCleanupEndF f) 20 :=
    hcontPrefixCleanupSeg (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123
      f.hlt125 f.hne125 f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5
      f.hugt f.hread35 f.hb13 f.hb32 f.hbne13 f.hend f.h8end f.hbit f.h8c f.hc110
      f.hc116 f.hceq116 f.r₁ f.r₂ f.r₃ f.ev f.hTail
  -- the merge's step, one link, from the token record's register
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G)
      (C := TailCarryEnd (ContTailStartC C) f.ev) (s := contCleanupEndF f) hsegP.inv' rfl
      (tok := C.stage.tok) (contCleanupEndF_tok f)
  -- the tail's `if` is its else arm, so the block it leaves is the merge's entry
  have hpc : (contCleanupEndF f).pc = "if.end473.i" :=
    contCleanupEnd_pc C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.r₁ f.r₂ f.r₃
      f.cA f.rdv f.xA
  rw [hpc] at hs₂
  have hs₂' : s₂ = clnMergeS f := hs₂
  subst hs₂'
  -- the cells at the merge
  have hincM : lookupName (clnMergeS f).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [show (clnMergeS f).env = (contCleanupEndF f).env from rfl, contCleanupEndF_inc]
    exact hInv.inc_reg
  have hnepM : lookupName (clnMergeS f).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [show (clnMergeS f).env = (contCleanupEndF f).env from rfl, contCleanupEndF_nep]
    exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  refine ⟨hsegP.trans (WalkSegment.of_link hl₂), hl₂.inv', rfl, rfl, clnMergeC_k C f.ev,
    hincM, hnepM, ?_⟩
  -- the price: the path is twenty-one links and the byte term is zero
  have hΔ : C.k + 1 - C.k = 1 := by omega
  simp only [stage2EntryAllowance, hΔ, Nat.mul_one]
  decide

/-! ### The `∀`-form, and the consumer that reads it

The form below is a `∀` over *head states* with the scan-free bundle, whose endpoint is the
composition's own term.  That is the shape `walkDispatch_at_continue_cells` reads its three
cells at, which is why the consumer compiles against it and not against an unrestricted
premise over segments.

Two of the three conjuncts are `WalkInv`-clause candidates and one is not: the index
equation relates two carries, and `WalkInv G C s` is indexed by one.  So the `∀`-form's
conclusion groups them the way the premise does, so that a consumer can see the same three
facts in the same order.

**This form is the scan-free arm's.**  The whitespace arm's cells are the same three facts
read at its latch-and-scan endpoint; its composition is `walkRevolutionMergeSegWs`, which
derives the run with `contWsRunF` and is stated below, because the whitespace arm's dispatch
is not this module's composition to prove.  Keeping one form over the arm whose segment this
module builds is what stops the two arm's cells being read at each other's endpoints. -/

/-- **The scan-free continuing entry's merge cells, at every head state with a bundle.**
The endpoint is the composition's own `clnMergeS`, so nothing is quantified over states the
run does not reach; the three conjuncts are the merge's own, in the producer's order. -/
theorem walkMergeCells_cleanup {m0 : Mem} (G : WalkGeom m0) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      (f : HcontCleanupFacts G C s) →
      ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
        Cd.block = "cleanup478.i" ∧ WalkInv G Cd sd ∧ sd.pre = some "if.end473.i" ∧
        (Cd.k = C.k ∧
          lookupName sd.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
          lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))) ∧
        p + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) := by
  intro C s hInv hblock f
  obtain ⟨hseg, hInvD, hblockD, hpre, hkC, hinc, hnep, hprice⟩ :=
    walkRevolutionMergeSeg G C s hInv hblock f
  exact ⟨clnMergeC C f.ev, clnMergeS f, 21, hseg, hblockD, hInvD, hpre,
    ⟨hkC, hinc, hnep⟩, hprice⟩

/-- **`WalkDispatch`'s body for a scan-free continuing entry, from the cells instead of a
premise.**  This is the dispatch body built on this module's producer: the segment comes
from `walkRevolutionMergeSeg`, which states the three cells at its own endpoint, so no fact
about an arbitrary segment is needed.

The depth is the invariant's (`depth_reg`, `depth_cap`, `sp_le_wlen`); the index and the two
register cells are the composition's.  The contract's byte term is a credit this arm does
not spend — the path's price `21 + 2 ≤ 32·Δk` holds with no byte term at all — so the
statement keeps the contract's shape and the proof discharges it from the smaller bound. -/
theorem walkDispatch_at_continue_cells {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (hcont : HcontCleanupFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      Cd.k = C.k ∧
      sd.pre = some prev ∧
      phiIncoming prev cleanupSpIncoming = some spOp ∧
      evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)) ∧
      phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧
      k2 < nepv.toNat ∧
      k2 < G.nep ∧
      C.k < k2 ∧
      spv ≤ stage2StackExtent ∧
      spv ≤ Cd.wlen ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) := by
  obtain ⟨hseg, hInvD, hblock, hpre, hkC, hinc, hnep, hprice⟩ :=
    walkRevolutionMergeSeg G C s hInv hhead hcont
  have hdepth : evalOperand (clnMergeS hcont) (Operand.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 (clnMergeC C hcont.ev).sp)) := hInvD.depth_reg
  have hincv : evalOperand (clnMergeS hcont) (Operand.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := hinc
  have hnep64 : G.nep < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
  refine ⟨clnMergeC C hcont.ev, clnMergeS hcont, 21, (clnMergeC C hcont.ev).sp,
    C.k + 1, "if.end473.i", Operand.reg "%sp.i.0248", Operand.reg "%inc.i",
    BitVec.ofNat 64 G.nep, hseg, hblock, hkC, hpre, (by decide), hdepth, (by decide),
    hincv, hnep, ?_, hk, ?_, hInvD.depth_cap, hInvD.sp_le_wlen, ?_⟩
  · rw [hnepv]; exact hk
  · omega
  · -- the price, with the contract's byte term as the credit it is
    have hΔ : C.k + 1 - C.k = 1 := by omega
    have h0 : 0 ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) := Nat.zero_le _
    simp only [stage2EntryAllowance, hΔ, Nat.mul_one] at hprice ⊢
    omega

/-- **`WalkDispatch`, from the scan-free continuing entry's premise and the head cells.**
The bridge `walkDispatch_of_continue` proves, with the producer of the three cells at the
head state's own segment: the hypotheses are per-state facts, the quantification is the
dispatch's, and nothing is assumed about a segment the producer did not build.

**The bridge's first hypothesis is spelled out rather than named.**  It is the scan-free
bundle's `∀`-form, whose declaration is `JsonStage2WalkPremisesOfStaging`'s; this module
does not import that one, because the consumers of the continuing entry's premise read the
cells from here and must be able to import *this* module.  The type is written out — it is
the same proposition, definitionally — rather than named across an import that would close
the direction.

The conclusion is `WalkDispatch`'s own body; the two `phiIncoming` cells are `decide`s on
`cleanupSpIncoming`/`cleanupKIncoming` rather than that module's named lemmas, for the same
reason. -/
theorem walkDispatch_of_continue_cells {m0 : Mem} {G : WalkGeom m0}
    (hcont : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → HcontCleanupFacts G C s) :
    WalkDispatch (stage2Calls stage2SubCalls) G := by
  intro C s hInv hhead hk
  exact walkDispatch_at_continue_cells C s hInv hhead hk (hcont C s hInv hhead hk)

/-! ### The whitespace arm's composition

The other arm: the head's eight links, the run and the seam (the run by `contWsRunF`), the
class-C span, the tail, the scan's three links, the visits, the exit and the merge.  Its
count is `(((8 + N) + 5) + 3 + 3) + nSc + 1 + 1`, where `N` is the run's own count, and its
price `p + 2 ≤ 32·Δk + 8·ΔA` — the byte term is the arm's own, because the scan's visits
are paid by the entry's span (`contWsPriceF`, `scanWsRounds`).  `hopS` is *produced* here
(`contWsEntry_hopS`), so the bundle carries no landing index.

The endpoint is `revMergeS sm v.toNat` at `revMergeC Cm`: the scan's exit's state at the
merge's block, which is where the three cells are read. -/
theorem walkRevolutionMergeSegWs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (f : HcontFacts G C s) :
    ∃ (Cm : WalkCarry G) (sm : State) (N nSc : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s (revMergeC Cm)
        (revMergeS sm f.v.toNat) ((((8 + N) + 5) + 3 + 3) + nSc + 1 + 1) ∧
      WalkInv G (revMergeC Cm) (revMergeS sm f.v.toNat) ∧
      (revMergeC Cm).block = "cleanup478.i" ∧
      (revMergeS sm f.v.toNat).pre = some "if.end473.i" ∧
      (revMergeC Cm).k = C.k ∧
      lookupName (revMergeS sm f.v.toNat).env "%inc.i" =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName (revMergeS sm f.v.toNat).env "%nep" =
        some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      nSc ≤ 4 * (f.v.toNat - 1 - f.k) ∧
      ((((8 + N) + 5) + 3 + 3) + nSc + 1 + 1) + 2 ≤
        stage2EntryAllowance * (C.k + 1 - C.k) +
          stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  -- 1. the head path to the whitespace check: eight links
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C)
      (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 8 :=
    contPrefixLand (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt
      f.hread35
  -- 2. the run and the seam, derived from the bundle's class: from the whitespace check's
  -- target to the seam, at the count and the stop's own cell the producer returns
  obtain ⟨N, hN, hsegRun, hcond⟩ := contWsRunF G C s f hseg8.inv' hk
  -- 3. the class-C span
  have hsegC : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1)
      (ContTailStartC C)
      (contWsTailStart C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1 f.x1)
      5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1)
      hsegRun.inv' rfl f.h8c f.hc110 f.hc116 f.hceq116
  -- 4. the tail's three calls
  have hsegT : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1 f.x1)
      (TailCarryScan (ContTailStartC C) f.ev) (contWsEntryF f) 3 := f.hTail
  -- 5. the scan's three links, from the produced selection
  have hsegL : WalkSegment (stage2Calls stage2SubCalls) G
      (TailCarryScan (ContTailStartC C) f.ev) (contWsEntryF f) (ContLatchC C f.ev)
      (contWsLatchF f) 3 := by
    obtain ⟨s', hs', hseg⟩ :=
      walkScanLinks457 (calls := stage2Calls stage2SubCalls) (G := G)
        (C := TailCarryScan (ContTailStartC C) f.ev) (s := contWsEntryF f) f.hTail.inv' rfl
        (contWsEntry_pre f) hlastEntry_phiSel (contWsEntry_hopS f) f.h3S f.hpos f.hreadS
        f.hbsS f.hloc105 f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
    rw [hs'] at hseg
    exact hseg
  have hsegP : WalkSegment (stage2Calls stage2SubCalls) G C s (ContLatchC C f.ev)
      (contWsLatchF f) (((8 + N) + 5) + 3 + 3) :=
    (((hseg8.trans hsegRun).trans (Seg.measure hsegC)).trans hsegT).trans hsegL
  -- 6. the latch's cells, and the visits with the merge's registers at the last one
  have hcounter : lookupName (contWsLatchF f).env "%q.0.i246" =
      some (.int 64 (BitVec.ofNat 64 f.k)) :=
    latch_counter (contWsEntryF f) (BitVec.ofNat 64 f.k) f.a f.q f.x47
  have hbound : lookupName (contWsLatchF f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := contWsLatch_cond f hcond
  have hinc0 : lookupName (contWsLatchF f).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [contWsLatch_inc]
    exact contWsSeamS_inc C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1
      hsegRun.inv'
  have hnep0 : lookupName (contWsLatchF f).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [contWsLatch_nep]
    exact contWsSeamS_nep C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1
      hsegRun.inv'
  have hk0 : (ContLatchC C f.ev).k = C.k := rfl
  obtain ⟨Cm, sm, nSc, hsegS, hInvR, hbR, hkR, hiR, hcR, hincR, hnepR, hnR⟩ :=
    scanWsRounds (G := G) (C := C) (s := s) f hsegP.inv' rfl hcounter hbound hinc0 hnep0
      hk0 f.heicd
  have hc64 : f.v.toNat < 2 ^ 64 := by have := f.v.isLt; omega
  have heicd := f.heicd
  -- 7. the exit: the inner budget is the invariant's local clause at the counts
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hinner : f.v.toNat - (f.v.toNat - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR hc64 (by omega)
  have hie : (f.v.toNat - 1) + 1 = f.v.toNat := by omega
  obtain ⟨s₁, hseg₁, hpc₁, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie hc64 (by intro e _ _ _; simp [WalkLocal])
  have hs₁' : s₁ = revExitS sm f.v.toNat := hs₁
  subst hs₁'
  -- 8. the merge, one step, from the token record's register
  obtain ⟨tok, htok⟩ := f.htok Cm sm hInvR hbR
  have htok₁ : lookupName (revExitS sm f.v.toNat).env "%t352.i" = some (.ptr tok) :=
    scanExit_tok sm (f.v.toNat - 1) f.v.toNat htok
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := revExitC Cm)
      (s := revExitS sm f.v.toNat) hInv₁ rfl htok₁
  have hs₂' : s₂ = revMergeS sm f.v.toNat := hs₂
  subst hs₂'
  -- the cells at the merge
  have hincM : lookupName (revMergeS sm f.v.toNat).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [revMergeS_inc, revExitS_inc, hincR]
  have hnepM : lookupName (revMergeS sm f.v.toNat).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [revMergeS_nep, revExitS_nep, hnepR]
  have hkM : (revMergeC Cm).k = C.k := by
    rw [revMergeC_k]; rw [hkR]
  have hpreM : (revMergeS sm f.v.toNat).pre = some "if.end473.i" := by
    simp only [revMergeS, hpc₁]
  refine ⟨Cm, sm, N, nSc, ?_, hl₂.inv', rfl, hpreM, hkM, hincM, hnepM, hnR, ?_⟩
  · exact (((hsegP.trans hsegS).trans hseg₁).trans (WalkSegment.of_link hl₂))
  · -- the price: the run's own bound and the scan's visits against the entry's span
    have hp := contWsPriceF G C s f hN
    have hΔ : C.k + 1 - C.k = 1 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one] at hp ⊢
    omega

/-- **`WalkDispatch`'s body on the whitespace arm.**  `walkRevolutionMergeSegWs`'s endpoint
and its three cells, in the dispatch's own shape: the index is `C.k + 1` (the header's
increment, which `%inc.i` carries to the merge), the depth is the invariant's, and the price
is the arm's own `p + 2 ≤ 32·Δk + 8·ΔA`. -/
theorem walkDispatch_at_continue_cells_ws {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (hcont : HcontFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      Cd.k = C.k ∧
      sd.pre = some prev ∧
      phiIncoming prev cleanupSpIncoming = some spOp ∧
      evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)) ∧
      phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧
      k2 < nepv.toNat ∧
      k2 < G.nep ∧
      C.k < k2 ∧
      spv ≤ stage2StackExtent ∧
      spv ≤ Cd.wlen ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) := by
  obtain ⟨Cm, sm, N, nSc, hseg, hInvD, hblock, hpre, hkC, hinc, hnep, -, hprice⟩ :=
    walkRevolutionMergeSegWs G C s hInv hhead hk hcont
  have hdepth : evalOperand (revMergeS sm hcont.v.toNat) (Operand.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 (revMergeC Cm).sp)) := hInvD.depth_reg
  have hincv : evalOperand (revMergeS sm hcont.v.toNat) (Operand.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := hinc
  have hnep64 : G.nep < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnepv : (BitVec.ofNat 64 G.nep).toNat = G.nep := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
  refine ⟨revMergeC Cm, revMergeS sm hcont.v.toNat, (((8 + N) + 5) + 3 + 3) + nSc + 1 + 1,
    (revMergeC Cm).sp, C.k + 1, "if.end473.i", Operand.reg "%sp.i.0248",
    Operand.reg "%inc.i", BitVec.ofNat 64 G.nep, hseg, hblock, hkC, hpre, (by decide),
    hdepth, (by decide), hincv, hnep, ?_, hk, ?_, hInvD.depth_cap, hInvD.sp_le_wlen,
    hprice⟩
  · rw [hnepv]; exact hk
  · omega

/-- **The whitespace arm's merge cells, at every head state with an entry left and a
bundle.**  The `∀`-form the loop's step reads for the `ws` arm, with the endpoint the
composition's own term.  The count premise is the bundle's own class field's supply: the
run is derived only where the stream continues past this entry. -/
theorem walkMergeCells_ws {m0 : Mem} (G : WalkGeom m0) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → (f : HcontFacts G C s) →
      ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
        Cd.block = "cleanup478.i" ∧ WalkInv G Cd sd ∧ sd.pre = some "if.end473.i" ∧
        (Cd.k = C.k ∧
          lookupName sd.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
          lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))) ∧
        p + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) +
          stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  intro C s hInv hblock hk f
  obtain ⟨Cm, sm, N, nSc, hseg, hInvD, hblockD, hpre, hkC, hinc, hnep, -, hprice⟩ :=
    walkRevolutionMergeSegWs G C s hInv hblock hk f
  exact ⟨revMergeC Cm, revMergeS sm f.v.toNat, (((8 + N) + 5) + 3 + 3) + nSc + 1 + 1,
    hseg, hblockD, hInvD, hpre, ⟨hkC, hinc, hnep⟩, hprice⟩

/-! ### The one conjunct the two clauses would not buy

`WalkInv.blockIndex` reads `%k.0.i249` at the carried index, and `while.body.i` is the only
block that binds that name (`whileBodyInstrs`' first `phi`, whose incoming from
`cleanup478.i` is `%k.2.i`).  So the premise's **first** conjunct is a fact about the
*endpoint*: the carry's index is whatever the state's block cell says, by `blockIndex` and
injectivity of `ofNat` below `2^64`.  The other two are the register cells.

That is the wall's shape, stated: adding the two clauses (`%inc.i`, `%nep`) retires the
premise's second and third conjuncts and leaves this one, which `blockIndex` already derives
once the endpoint's cell is known.  `walkRevolutionMergeSeg` supplies the cell
(`contLatchF_inc` transports the head's, and the scan's rounds keep it), which is why the
producer's three facts are one composition rather than three premises. -/

/-- **The merge's carry index is the endpoint's block cell.**  No run is needed: the carry is
`blockIndex`'s value at any state whose `%k.0.i249` is `ofNat 64 k`. -/
theorem mergeK_of_blockIndex {m0 : Mem} {G : WalkGeom m0} {Cd : WalkCarry G} {sd : State}
    (hInvD : WalkInv G Cd sd) {k : Nat}
    (hk0 : lookupName sd.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 k)))
    (hk64 : k < 2 ^ 64) : Cd.k = k := by
  have hb := hInvD.blockIndex
  rw [hk0] at hb
  have heq : BitVec.ofNat 64 Cd.k = BitVec.ofNat 64 k := by
    have h2 := Option.some.inj hb
    simp only [Value.int.injEq] at h2
    exact (eq_of_heq h2.2).symm
  -- the two readings agree below `2^64`
  have hmax : G.n ≤ 2 ^ 32 := by
    have := G.maxDoc
    simpa only [stage2MaxDocument] using this
  have hkCd : Cd.k < 2 ^ 64 := by
    have h := hInvD.k_le
    have h2 := G.nep_le
    omega
  have hn := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkCd,
    Nat.mod_eq_of_lt hk64] at hn
  omega

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scanRoundSeg4
#print axioms LeanLLVM.Refinement.WalkScope.scanWsRounds
#print axioms LeanLLVM.Refinement.WalkScope.contCleanupEndF_inc
#print axioms LeanLLVM.Refinement.WalkScope.contCleanupEndF_nep
#print axioms LeanLLVM.Refinement.WalkScope.contCleanupEndF_tok
#print axioms LeanLLVM.Refinement.WalkScope.walkRevolutionMergeSeg
#print axioms LeanLLVM.Refinement.WalkScope.mergeHeadCells
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadCells
#print axioms LeanLLVM.Refinement.WalkScope.walkMergeCells_cleanup
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_continue_cells
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_of_continue_cells
#print axioms LeanLLVM.Refinement.WalkScope.contWsEntry_hopS
#print axioms LeanLLVM.Refinement.WalkScope.walkRevolutionMergeSegWs
#print axioms LeanLLVM.Refinement.WalkScope.walkMergeCells_ws
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_continue_cells_ws
#print axioms LeanLLVM.Refinement.WalkScope.mergeK_of_blockIndex

end WalkScope
end LeanLLVM.Refinement
