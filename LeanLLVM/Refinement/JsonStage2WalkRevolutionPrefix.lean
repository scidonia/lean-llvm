/-
The continuing entry's path to the extra-token scan, counted.

## The arm, and why it is not `hlastPrefixSeg`'s

`walkRevolution_seg` composes a segment from the loop head to `cleanup478.i` for an entry
with another entry after it, and the prefix it used was `hlastPrefixSeg`'s — the **last**
entry's.  That prefix takes `sw.default.i`'s count test on its failing arm
(`cond.end349.i`); a continuing entry passes the test, so its path leaves through
`cond.true345.i`, which reads the *next* entry's position lane and zero-extends it into
`%conv347.i`.  The prefix here is that arm: the same four high-byte pivots and the same
`sw.default.i` link, then `cond.true345.i` and `cond.end349.i`.

Five premises carry this path that the last entry's does not:

* the next entry's lane — `%5`'s pointer, `%inc.i`'s value and the word the load reads —
  the three facts `cond.true345.i`'s step needs, and the reason the `phi`'s value at
  `cond.end349.i` is `ofNat 64 v.toNat` rather than a caller-supplied word;
* the count test's **value** is `1` (`hnext`), not `0`;
* `%cond350.i` is therefore the entry's own end, above its start (`hugt`, `= 1`), so
  `cond.end349.i` takes `land.lhs.true357.i`: the entry is non-empty and the walk reads
  the byte just before its end (`b35`, `hread35`);
* that byte is not whitespace, which is the three pivot bits `hb13`/`hb32`/`hbne13` — the
  class the price's own longest path names (`NodeBlock41 → NodeBlock39 → LeafBlock35`)
  and the reason `if.end372.i` is reached without the whitespace run;
* the entry's first byte is below `125` on all four of the head's pivots (`hlt91` etc.,
  the same class `hlastPrefixSeg` takes) and is not `-`/digit (`hbit`), so the class-C
  span of the head path (`walkHeadChainCSeg`) is the tail's route.

## Which of `hlastPrefixSeg`'s links are reused

The four pivots (`NodeBlock21`, `NodeBlock19`, `NodeBlock17`, `LeafBlock15`) and
`sw.default.i` are the same links at the same states: `walkHeadChainASeg`'s first five
steps, whose carries `HeadAC₁`…`HeadAC₄` and states `headAS₁`…`headAS₄` this module
reuses unchanged.  What is not shared is everything from `cond.end349.i` on: the last
entry's `phi` selects `%4` at `headAS₅`, this one selects `%conv347.i` at the state
`cond.true345.i` leaves, and `%cond350.i` differs, so the token's end, the seam state and
the tail's start are **new states with new names** — `contEndS` … `contLatch`.  The class-C
span, the tail, the scan and their counted forms (`walkHeadChainCSeg`, `consumerTailSegAt`,
`walkScanLinks457`) are reused at the new names, because they are stated at their entry
state and not at the head.

**"The same shape" is true of the links and false of the states.**  A plan that says a new
path "is the rest of `hlastPrefixSeg`'s shape, and its links exist" is right about the
links and wrong about the composition: a `Segment`'s carries and states are **indices**,
and an index is unified syntactically, so a state that differs only in the `phi` arm its
predecessor took is a different index.  Here the count test's arm changes `%cond350.i` at
`cond.end349.i`, and that single change re-states the token's end, the seam, the tail's
start, the scan's entry and the latch — five states and the whole carry nest — while every
link below stays the one `hlastPrefixSeg` already uses.  The lesson is about plans rather
than proofs: "the same shape" is a statement about the *links*, and a segment is stitched
at its *states*.

## The count

| piece | links |
|---|---|
| the head: four pivots, `sw.default.i`, `cond.true345.i`, `cond.end349.i` | `7` |
| the whitespace check: `land.lhs.true357.i`, `NodeBlock41`, `NodeBlock39`, `LeafBlock35` | `4` |
| the seam `if.end372.i` | `1` |
| the class-C span `walkHeadChainCSeg` | `5` |
| the tail `consumerTailSegAt` | `3` |
| the scan `walkScanLinks457` | `3` |

`7 + 4 + 1 + 5 + 3 + 3 = 23`.  The consumer's price is the prefix plus the scan's `n`
visits, the latch's exit and the merge, plus the `2` the credit's statement adds:
`(23 + n + 1 + 1) + 2 = 27 + n`, against `32·Δk + 8·ΔA` at `Δk = 1`.  With `n ≤ 8·ΔA` that
is `27 + 8·ΔA ≤ 32 + 8·ΔA`, so the fixed part grows from the last entry's `22` to `27` and
still fits the entry allowance: the bound is not widened.

## The arm's boundary: this bundle's scan is entered only when a whitespace stops the token

The seam's `%ee.1.i` `phi` selects `%cond350.i` on the three leaf edges, so on this path
the token's end is the entry's end and the scan's index is that same word: `contEntry_ee`
is the peel, and `contEntry_scan_empty` proves `¬ (ei < v.toNat)` from it.  `if.then447.i`'s
target tests exactly `ult ei %cond350.i`, so on this path the walk does not enter the scan —
it goes to `if.end473.i` and straight to the merge.  **The bundle that carries `heicd`
therefore describes the whitespace arm only** (the byte before the entry's end is `9`,
`10`, `13` or `32`, the skip runs to the first whitespace byte `k`, and the scan runs
`[k, v.toNat)`); the no-whitespace classes need a scan-free sibling, which is cheaper.

## The classes still to write, and what they cost

`%35` — the byte before the entry's end — has six classes, and this prefix is the one with
no whitespace run: `13 ≤ %35 < 32` and `%35 ≠ 13`, so `NodeBlock41 → NodeBlock39 →
LeafBlock35 → if.end372.i`.  The other five are the same three pivots' other arms, and the
three of them whose byte *is* whitespace (`9`, `10`, `13`, `32`) enter
`land.rhs.i.preheader` and the skip `while.body370.i`.

**The run does not break `32·Δk`, and the reason is that it and the token scan split the
entry's span.**  Write `i` for `%idxprom.i` and `k` for the index the run stops at — the
first whitespace byte, which is the token's end `%ee.1.i`, so the token scan starts at `k`
and its visits are `cd - 1 - k`.  A continuing visit is at most five steps (`land.rhs.i`,
`NodeBlock52`, the leaf, and the latch's own step `while.body370.i → land.rhs.i`; a byte
below `13` reaches its leaf in one fewer), and the exit visit is at most four, so the run
costs `≤ 5·(k - i) + 4`.  The prefix is then `≤ 12 + (5·(k - i) + 4) + 12` — the head, the
three pivots and the preheader before the run, and the seam, the class-C span, the tail and
the scan after it — and the price is `p + 2 ≤ 30 + 5(k - i) + n` with `n ≤ 8(cd - 1 - k)`.
Since `5(k - i) + 8(cd - 1 - k) ≤ 8(k - i) + 8(cd - 1 - k) = 8(cd - 1 - i)` and
`cd - 1 - i < entryPos (C.k + 1) - entryPos C.k = ΔA`, that is `p + 2 ≤ 30 + 8·ΔA`:
inside `32·Δk + 8·ΔA`, with two steps to spare.  **The byte budget is not double-spent
precisely because the scan's start is the run's stop**; a prefix that let the scan start at
`i` while the run also ran would charge `8·ΔA` twice and the bound would fail.

**What the run costs to prove, and the layer gap it exposes.**  `WalkScanInduction.step`
(`JsonStage2WalkChain`) is the *latch's* step — `while.body370.i`'s increment and its
counter-versus-bound test, ending at `land.rhs.i` — not a visit: the dispatch
(`land.rhs.i → NodeBlock52 → leaf → while.body370.i`) is outside it, and its `exitStep` is
the counter reaching the bound, which the run never does (the byte at `cd - 1` is
whitespace by the guard, so the leaf exits first).  A run therefore needs, per visit, the
three dispatch links (`WalkLink.land_rhs_i_at`, `WalkLink.NodeBlock52_at`, the leaf's
`_at`) *and* `scanLatch_visit_at`, and each visit must rebuild the `WalkLocal` at
`while.body370.i` — the `ScanCount`/`ScanLanded` witness the induction's `step` body
constructs — from the document's byte at that index and its class.  The document's facts
are per-index, so the whitespace bundle carries them as a `∀` over the run's range (the
byte and the two pivot bits at each index), exactly as the class bits are carried for the
single byte here.

## `%cond350.i` is one number, not two

The scan's bound at the latch is the entry's end, which is the word `cond.true345.i`
loaded: `%cond350.i` is bound once, at `cond.end349.i`, and no block from there to the scan
rebinds it.  So the latch's `%cond350.i` is `ofNat 64 v.toNat` **by construction** and the
bundle carries no separate bound witness — `contLatch_cond` below is the peel that says
so.  The scan's first index `ei` and the entry's span stay the caller's: they are the
document's numbers.
-/

import LeanLLVM.Refinement.JsonStage2WalkPrefixCount

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### `cond.true345.i`: the next entry's lane

The block is `gep+load+zext` and ends in a `br`, so its successor is the state its own
`denoteCode` leaves.  `WalkLink.cond_true345_i` proves the link; this section names the
target so a segment can be threaded through it.
-/

/-- `cond.true345.i`'s target: the lane's address, the word and its zero-extension, at
`cond.end349.i`. -/
def cte345OutAt (s : State) (ep : Nat) (i : BitVec 64) (v : BitVec 32) : State :=
  { (stateAt (cells
      [("%conv347.i", .int 64 (BitVec.ofNat 64 v.toNat)),
       ("%34", .int 32 v),
       ("%arrayidx346.i", .ptr (ep + i.toNat * 4))] s.env) s) with
    pc := "cond.end349.i", pre := some s.pc }

/-- **`cond.true345.i`'s target, named.** -/
theorem WalkLink.cond_true345_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.true345.i")
    {ep : Nat} {i : BitVec 64} {v : BitVec 32}
    (h5 : lookupName s.env "%5" = some (.ptr ep))
    (hinc : lookupName s.env "%inc.i" = some (.int 64 i))
    (hi63 : i.toNat < 2 ^ 63)
    (hread : readBytes s.mem (ep + i.toNat * 4) 4 = some (natToBytes v.toNat 4)) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "cond.end349.i" } s' ∧
      s' = cte345OutAt s ep i v := by
  obtain ⟨s', hl⟩ :=
    WalkLink.cond_true345_i (calls := calls) G C s hInv hblock h5 hinc hi63 hread
  refine ⟨s', hl, ?_⟩
  have hden : denoteCode calls walkCond_true345_i.instrs s =
      some (stateAt (cells
        [("%conv347.i", .int 64 (BitVec.ofNat 64 v.toNat)),
         ("%34", .int 32 v),
         ("%arrayidx346.i", .ptr (ep + i.toNat * 4))] s.env) s) := by
    simp only [walkCond_true345_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep32_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx346.i")
      (base := "%5") (off := "%inc.i") (a := ep) (o := i) h5 hinc hi63]
    rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_load_i32 (calls := calls)
      (env := ("%arrayidx346.i", .ptr (ep + i.toNat * 4)) :: s.env) (s := s)
      (d := "%34") (p := "%arrayidx346.i") (a := ep + i.toNat * 4) (v := v)
      (by simp [lookupName]) hread]
    rw [denoteCode_zext (calls := calls)
      (env := ("%34", .int 32 v) :: ("%arrayidx346.i", .ptr (ep + i.toNat * 4)) :: s.env)
      (s := s) (d := "%conv347.i") (v := "%34") 32 64 (x := v) (by simp [lookupName])]
    rfl
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfind : stage2Body.findBlock s.pc = some walkCond_true345_i := by
    rw [hpc, hblock]; exact walkCond_true345_i_find
  have hterm : walkCond_true345_i.term = Term.br "cond.end349.i" := rfl
  have hstep : LeanLLVM.step calls stage2Body s = .jump (cte345OutAt s ep i v) := by
    simp only [LeanLLVM.step, hfind, hden, hterm, execTerm, cte345OutAt, stateAt, cells]
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- `%conv347.i` at the lane's target is the zero-extended word: the link's own cell. -/
theorem cte345OutAt_conv (s : State) (ep : Nat) (i : BitVec 64) (v : BitVec 32) :
    lookupName (cte345OutAt s ep i v).env "%conv347.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [cte345OutAt, stateAt, cells]
  exact lookupName_cons_self _ _ _

/-! ### The continuing entry's states, named

Every state from `cond.end349.i` on is a name, because each is where a link's hypotheses
are read and where the next link's source must be the same *term*. -/

/-- The state `sw.default.i` leaves on the succeeding arm: the count test's cell, at
`cond.true345.i`.  It is `headAS₅`'s environment and memory with the other edge's `pc`,
which is why it is a name of its own: a `Segment`'s state is an index and the two edges'
targets are different terms. -/
def contAS₅ (s : State) (x : BitVec 8) (inc nep : BitVec 64) : State :=
  { (headAS₄ s x).bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep)) with
    pc := "cond.true345.i", pre := some (headAS₄ s x).pc }

/-- The byte `land.lhs.true357.i` loads, as the `%35` cell holds it. -/
abbrev cont35 (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat

/-- `cond.end349.i`'s target on the continuing arm: its source is `cond.true345.i`'s
target, so the bound's `phi` selects `%conv347.i` and `%cond350.i` is `ofNat 64 v.toNat`. -/
def contEndS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) : State :=
  condEnd349OutAt (cte345OutAt (contAS₅ s x inc nep) ep inc v)
    (BitVec.ofNat 64 v.toNat) ix C.stage.tok (C.stage.tok + 20)

/-- `land.lhs.true357.i`'s target: the byte before the entry's end and its address. -/
def contLandS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { (stateAt (cells [("%35", .int 8 (cont35 b35)), ("%gep", .ptr ((G.b - 1) + v.toNat))]
      (contEndS C s x inc nep ep v ix).env) (contEndS C s x inc nep ep v ix)) with
    pc := "NodeBlock41", pre := some (contEndS C s x inc nep ep v ix).pc }

/-- `NodeBlock41`'s target, on the arm its `%35 < 13` test does not take. -/
def contP41S {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((contLandS C s x inc nep ep v ix b35).bind "%Pivot42"
      (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some (contLandS C s x inc nep ep v ix b35).pc }

/-- `NodeBlock39`'s target, on the arm its `%35 < 32` test takes. -/
def contP39S {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((contP41S C s x inc nep ep v ix b35).bind "%Pivot40"
      (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock35", pre := some (contP41S C s x inc nep ep v ix b35).pc }

/-- `LeafBlock35`'s target, on the arm its `%35 = 13` test does not take: the token's
end. -/
def contP35S {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) : State :=
  { ((contP39S C s x inc nep ep v ix b35).bind "%SwitchLeaf36"
      (.int 1 (evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "if.end372.i", pre := some (contP39S C s x inc nep ep v ix b35).pc }

/-- The seam: `if.end372.i`'s else arm, at the class-C span's entry.  The token's end
`phi` selects `%cond350.i` here — the entry's end — so the stored end is `ofNat 64 v.toNat`. -/
def contSeamS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) : State :=
  seamS (contP35S C s x inc nep ep v ix b35) (BitVec.ofNat 64 v.toNat) b8 C.stage.tok

/-- The class-C span's target: the value-position call's block. -/
def contTailStart {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) : State :=
  HeadS413 (contSeamS C s x inc nep ep v ix b35 b8) x1

/-- The scan's entry: the tail's end state, at the block `%cond350.i` makes `v.toNat`. -/
def contEntry {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei : Nat) (cA rdv xA : BitVec 32) : State :=
  ScanEntry (contTailStart C s x inc nep ep v ix b35 b8 x1) r₁ r₂ r₃ ei v.toNat cA rdv xA

/-- The scan's latch. -/
def contLatch {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) : State :=
  Latch462S (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA) idx a q x47

/-! ### The cells the path's own states carry

`%cond350.i` is bound once — at `cond.end349.i` — and no block from there to the latch
rebinds it, so the latch's bound is the lane's word and not a second witness.  `%35` is
the byte `land.lhs.true357.i` loaded, `%8` is the loop head's. -/

/-- The latch's bound: `ofNat 64 v.toNat`, peeled from `cond.end349.i`'s own cell through
the seam, the class-C span, the tail and the scan. -/
theorem contLatch_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 x1 : BitVec 8) (r₁ r₂ r₃ : CallOutcome) (ei : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) :
    lookupName (contLatch C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA idx a q x47).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contLatch, contEntry, ScanEntry, contTailStart, HeadS413, HeadS405, HeadS58,
    HeadS60, HeadS62, contSeamS, seamS, seamFin, contP35S, contP39S, contP41S, contLandS,
    contEndS, cte345OutAt, condEnd349OutAt, TailS₃, landRhs457OutAt,
    stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _


/-! ### The carries, named

Each link's target is the previous carry with one `block` update; the nest grows one level
per link, so each level is an `abbrev` — a depth-three `with`-nest is not a term a named
argument can hold.  The sequence starts at `HeadAC₄` (the four pivots' target, shared with
`walkHeadChainASeg`) and does *not* pass through `HeadAC₅`: the count test's succeeding arm
is `cond.true345.i`, a different block. -/

/-- The carry at `cond.true345.i`: the count test's *succeeding* arm. -/
abbrev ContAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₄ C with block := "cond.true345.i" }

/-- The carry at `cond.end349.i`, reached from `cond.true345.i`. -/
abbrev ContAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₁ C with block := "cond.end349.i" }

/-- The carry at the whitespace check: the entry's end is above its start. -/
abbrev ContAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₂ C with block := "land.lhs.true357.i" }

/-- The carry at the byte's first pivot. -/
abbrev ContAC₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₃ C with block := "NodeBlock41" }

/-- The carry at the byte's second pivot. -/
abbrev ContAC₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₄ C with block := "NodeBlock39" }

/-- The carry at the leaf the byte's class selects. -/
abbrev ContAC₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₅ C with block := "LeafBlock35" }

/-- The carry at the token's end `if.end372.i`. -/
abbrev ContAC₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₆ C with block := "if.end372.i" }

/-- The carry at the class-C span's entry. -/
abbrev ContSeamC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { ContAC₇ C with block := "if.else387.i" }

/-- The tail's start carry: the class-C span's target. -/
abbrev ContTailStartC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  HeadC₄₁₃ (ContSeamC C)

/-- The scan's latch carry. -/
abbrev ContLatchC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }

/-! ### The cells the path reads

Each is a peel: the block that bound it is one of the path's own. -/

/-- `%inc.i` at the succeeding arm is the loop head's. -/
theorem contAS₅_envInc (s : State) (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%inc.i" = some (.int 64 inc)) :
    lookupName (contAS₅ s x inc nep).env "%inc.i" = some (.int 64 inc) := by
  simp only [contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%idxprom.i` at `cond.true345.i`'s target is the loop head's. -/
theorem cte345OutAt_envIdx (s : State) (ep : Nat) (i : BitVec 64) (v : BitVec 32) :
    lookupName (cte345OutAt s ep i v).env "%idxprom.i" = lookupName s.env "%idxprom.i" := by
  simp only [cte345OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%t352.i` at the same state. -/
theorem cte345OutAt_envTok (s : State) (ep : Nat) (i : BitVec 64) (v : BitVec 32) :
    lookupName (cte345OutAt s ep i v).env "%t352.i" = lookupName s.env "%t352.i" := by
  simp only [cte345OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%gap.i` at the same state. -/
theorem cte345OutAt_envGap (s : State) (ep : Nat) (i : BitVec 64) (v : BitVec 32) :
    lookupName (cte345OutAt s ep i v).env "%gap.i" = lookupName s.env "%gap.i" := by
  simp only [cte345OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The bound's `phi` at `cond.end349.i`'s target selects `%conv347.i` on this edge. -/
theorem contPhi6 :
    phiIncoming "cond.true345.i"
      [("cond.true345.i", Operand.reg "%conv347.i"),
       ("sw.default.i", Operand.reg "%4")] = some (.reg "%conv347.i") := by
  decide

/-- The token's end's `phi` selects `%cond350.i` when the whitespace check is what sent
the walk there. -/
theorem contPhiSeam :
    phiIncoming "LeafBlock35"
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some (.reg "%cond350.i") := by
  decide

/-- `%cond350.i` at the token's end is the entry's end: `cond.end349.i` bound it once. -/
theorem contEndS_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) :
    lookupName (contEndS C s x inc nep ep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contEndS, condEnd349OutAt, cells]
  rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%35` at the whitespace check's target. -/
theorem contLandS_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contLandS C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contLandS, stateAt, cells]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's first pivot. -/
theorem contP41S_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contP41S C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contP41S, contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's second pivot. -/
theorem contP39S_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contP39S C s x inc nep ep v ix b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contP39S, contP41S, contLandS, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the token's end. -/
theorem contP35S_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contP35S C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contP35S, contP39S, contP41S, contLandS, contEndS, condEnd349OutAt, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%ee.1.i` at the scan's entry is the token's end the seam stored: the phi selects it on
`if.then447.i`'s edge and nothing between the seam and the tail's end rebinds it. -/
theorem contEntry_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 x1 : BitVec 8) (r₁ r₂ r₃ : CallOutcome) (ei : Nat)
    (cA rdv xA : BitVec 32) :
    lookupName (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
      "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contEntry, ScanEntry, TailS₃, TailS₂, TailS₁, contTailStart, HeadS413, HeadS405,
    HeadS58, HeadS60, HeadS62, contSeamS, seamS, seamFin, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- **The extra-token scan is entered at the token's end, so this arm's span is empty.**
The scan's counter phi selects `%ee.1.i` on `if.then447.i`'s edge, and that cell is the
seam's stored end — `ofNat 64 v.toNat` — so the bundle's scan index `ei` is that word and
"the span is non-empty" (`heicd`) is `v.toNat < v.toNat`.

This is the arm's own arithmetic, not a hypothesis: the guard the scan is entered on is
`ult ei %cond350.i`, and on the no-whitespace arm the token's end *is* the entry's end.
The walk therefore skips the scan and reaches `if.end473.i` directly. -/
theorem contEntry_scan_empty {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 x1 : BitVec 8) (r₁ r₂ r₃ : CallOutcome) (ei : Nat)
    (cA rdv xA : BitVec 32)
    (hop : evalOperand (stateAt
      (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
      (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)) (.reg "%ee.1.i") =
      some (.int 64 (BitVec.ofNat 64 ei))) :
    ¬ ei < v.toNat := by
  have hcell := contEntry_ee C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA
  have hlook : lookupName
      (stateAt (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
        (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)).env "%ee.1.i" =
      some (Value.int 64 (BitVec.ofNat 64 v.toNat)) := by
    simpa only [stateAt] using hcell
  have hbit : BitVec.ofNat 64 ei = BitVec.ofNat 64 v.toNat := by
    have h2 : some (Value.int 64 (BitVec.ofNat 64 ei)) =
        some (Value.int 64 (BitVec.ofNat 64 v.toNat)) := by
      simpa only [evalOperand, hlook] using hop.symm
    have h3 := Option.some.inj h2
    simp only [Value.int.injEq] at h3
    exact eq_of_heq h3.2
  intro hlt
  have hmod : ei % 2 ^ 64 = v.toNat := by
    have h4 := congrArg BitVec.toNat hbit
    simp only [BitVec.toNat_ofNat] at h4
    have hv64 : v.toNat % 2 ^ 64 = v.toNat :=
      Nat.mod_eq_of_lt (by have := v.isLt; omega)
    rw [hv64] at h4
    exact h4
  have hv : v.toNat < 2 ^ 32 := v.isLt
  have hei : ei < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hei] at hmod
  omega

/-! ### The prefix -/

/-- **A continuing entry's path to the extra-token scan, counted at twenty-three.**  The
four high-byte pivots and `sw.default.i`, the count test's *succeeding* arm
(`cond.true345.i`), the bound's `phi` (`cond.end349.i`), the whitespace check at the
entry's end (`land.lhs.true357.i` and the byte's three pivots), the token's end
(`if.end372.i`), the class-C span, the tail's three calls and the scan's three links.

The hypotheses are the path's inputs, grouped as the references read them: the head's byte
and its four pivot bits, the counts and the test's value, the next entry's lane (pointer,
word and read), the bound's position against the entry's index, the byte before the end
and its three class bits, the seam's byte and cells, the second byte's class, the tail's
counted segment at `3`, and the scan's landing. -/
theorem hcontPrefixSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    (h5 : lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contAS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx5 : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (contAS₅ s x inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
      some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35S C s x inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35S C s x inc nep ep v ix b35).env "%8" = some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    {x1 : BitVec 8}
    (h8c : evalOperand (contSeamS C s x inc nep ep v ix b35 b8) (.reg "%8") =
      some (.int 8 x1))
    (hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord)
    {cA rdv : BitVec 32} {xA : BitVec 32} {ei : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contTailStart C s x inc nep ep v ix b35 b8 x1)
      (TailCarryScan (ContTailStartC C) ev)
      (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA) 3)
    {a q : Nat} {bs : List UInt8} {src : String} {sel : Operand}
    (hpreS : (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).pre = some src)
    (hincS : phiIncoming src
      [("while.body462.i", (Operand.reg "%inc463.i")),
       ("if.then447.i", (Operand.reg "%ee.1.i"))] = some sel)
    (hopS : evalOperand (stateAt
      (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
      (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)) sel =
      some (.int 64 (BitVec.ofNat 64 ei)))
    (h3S : lookupName (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
      "%3" = some (.ptr a))
    (hpos : ((BitVec.ofNat 64 ei).signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes
      (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).mem
      (a + ((BitVec.ofNat 64 ei).signExtend 64).toNat) 1 = some bs)
    (hbsS : bytesToNat bs = q)
    (hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
      (landRhs457OutAt (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
        (BitVec.ofNat 64 ei) a q))
    {x47 : BitVec 8}
    (h47 : evalOperand
      (landRhs457OutAt (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
        (BitVec.ofNat 64 ei) a q) (.reg "%47") = some (.int 8 x47))
    (hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
      (ScanS₉₆ (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
        (BitVec.ofNat 64 ei) a q x47))
    (hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
      (contLatch C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA
        (BitVec.ofNat 64 ei) a q x47)) :
    ∃ (s' : State),
      s' = contLatch C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA
        (BitVec.ofNat 64 ei) a q x47 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContLatchC C ev) s' 23 := by
  -- the arms, resolved by the class's bits
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by
    rw [hlt91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock17" := by
    rw [hlt123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 125) = 1 then
      "LeafBlock13" else "LeafBlock15") = "LeafBlock15" := by
    rw [hlt125]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 125) = 1 then
      "if.then53.i" else "sw.default.i") = "sw.default.i" := by
    rw [hne125]; rfl
  have hres₅ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.true345.i" := by
    rw [hnext]; rfl
  -- the byte's operand fact at each pivot, peeled past the cells the pivots bind
  have h8₁ : evalOperand (headAS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₂ : evalOperand (headAS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₂, headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₃ : evalOperand (headAS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₃, headAS₂, headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot18") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (HeadAC₁ C) (headAS₁ s x) := by
    have hst : s₁ = headAS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. the second pivot
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (HeadAC₁ C)
      (headAS₁ s x) hl₁'.inv' rfl h8₁
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₁ C) (headAS₁ s x)
      (HeadAC₂ C) (headAS₂ s x) := by
    have hst : s₂ = headAS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the third pivot
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock17_at (calls := stage2Calls stage2SubCalls) G (HeadAC₂ C)
      (headAS₂ s x) hl₂'.inv' rfl h8₂
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₂ C) (headAS₂ s x)
      (HeadAC₃ C) (headAS₃ s x) := by
    have hst : s₃ = headAS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock15_at (calls := stage2Calls stage2SubCalls) G (HeadAC₃ C)
      (headAS₃ s x) hl₃'.inv' rfl h8₃
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₃ C) (headAS₃ s x)
      (HeadAC₄ C) (headAS₄ s x) := by
    have hst : s₄ = headAS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- 5. the default arm's entry count, on the succeeding arm
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (HeadAC₄ C)
      (headAS₄ s x) hl₄'.inv' rfl hinc hnep
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₄ C) (headAS₄ s x)
      (ContAC₁ C) (contAS₅ s x inc nep) := by
    have hst : s₅ = contAS₅ s x inc nep := by rw [hs₅, hres₅]; rfl
    rw [hst] at hl₅
    rw [hres₅] at hl₅
    exact hl₅
  -- 6. the next entry's position lane
  have hinc4 : lookupName (headAS₄ s x).env "%inc.i" = some (.int 64 inc) := by
    simpa only [evalOperand] using hinc
  have hinc5 : lookupName (contAS₅ s x inc nep).env "%inc.i" = some (.int 64 inc) :=
    contAS₅_envInc s x inc nep hinc4
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.cond_true345_i_at (calls := stage2Calls stage2SubCalls) G (ContAC₁ C)
      (contAS₅ s x inc nep) hl₅'.inv' rfl h5 hinc5 hi63 hread
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₁ C) (contAS₅ s x inc nep)
      (ContAC₂ C) (cte345OutAt (contAS₅ s x inc nep) ep inc v) := by
    rw [hs₆] at hl₆
    exact hl₆
  -- 7. the bound's `phi` and the position's compare, on the non-empty arm
  have hidx6 : lookupName (cte345OutAt (contAS₅ s x inc nep) ep inc v).env "%idxprom.i" =
      some (.int 64 ix) := by
    rw [cte345OutAt_envIdx]; exact hidx5
  have htok6 : lookupName (cte345OutAt (contAS₅ s x inc nep) ep inc v).env "%t352.i" =
      some (.ptr C.stage.tok) := by
    rw [cte345OutAt_envTok]; exact htok5
  have hgap6 : lookupName (cte345OutAt (contAS₅ s x inc nep) ep inc v).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)) := by
    rw [cte345OutAt_envGap]; exact hgap5
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.cond_end349_i_at G (ContAC₂ C)
      (cte345OutAt (contAS₅ s x inc nep) ep inc v) hl₆'.inv' rfl
      (p := "cond.true345.i") rfl contPhi6
      (cte345OutAt_conv (contAS₅ s x inc nep) ep inc v) hidx6 htok6 hgap6
  have hres₇ : (if evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₂ C)
      (cte345OutAt (contAS₅ s x inc nep) ep inc v) (ContAC₃ C)
      (contEndS C s x inc nep ep v ix) := by
    have hst : s₇ = contEndS C s x inc nep ep v ix := by
      rw [hs₇]
      rfl
    rw [hst] at hl₇
    rw [hres₇] at hl₇
    exact hl₇
  -- 8. the byte before the entry's end
  have hig : lookupName (contEndS C s x inc nep ep v ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    hl₇'.inv'.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (contEndS C s x inc nep ep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) :=
    contEndS_cond C s x inc nep ep v ix
  have hq63 : v.toNat < 2 ^ 63 := by
    have := v.isLt; omega
  obtain ⟨s₈, hl₈, hs₈⟩ :=
    WalkLink.land_lhs_true357_i_at G (ContAC₃ C) (contEndS C s x inc nep ep v ix)
      hl₇'.inv' rfl (ig := G.b - 1) (q := v.toNat) (b := b35) hig hcond hq63 hread35
  have hl₈' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₃ C)
      (contEndS C s x inc nep ep v ix) (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) := by
    rw [hs₈] at hl₈
    exact hl₈
  -- 9. the byte's first pivot
  have h35a : evalOperand (contLandS C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandS_35 C s x inc nep ep v ix b35
  obtain ⟨s₉, hl₉, hs₉⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hl₈'.inv' rfl h35a
  have hl₉' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) (ContAC₅ C)
      (contP41S C s x inc nep ep v ix b35) := by
    have hst : s₉ = contP41S C s x inc nep ep v ix b35 := by
      rw [hs₉, show (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" from by rw [hb13]; rfl]
      rfl
    rw [hst] at hl₉
    rw [show (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
      "LeafBlock33" else "NodeBlock39") = "NodeBlock39" from by rw [hb13]; rfl] at hl₉
    exact hl₉
  -- 10. the byte's second pivot
  have h35b : evalOperand (contP41S C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP41S_35 C s x inc nep ep v ix b35
  obtain ⟨s₁₀, hl₁₀, hs₁₀⟩ :=
    WalkLink.NodeBlock39_at (calls := stage2Calls stage2SubCalls) G (ContAC₅ C)
      (contP41S C s x inc nep ep v ix b35) hl₉'.inv' rfl h35b
  have hl₁₀' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₅ C)
      (contP41S C s x inc nep ep v ix b35) (ContAC₆ C)
      (contP39S C s x inc nep ep v ix b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := by rw [hb32]; rfl
    have hst : s₁₀ = contP39S C s x inc nep ep v ix b35 := by rw [hs₁₀, harm]; rfl
    rw [hst] at hl₁₀
    rw [harm] at hl₁₀
    exact hl₁₀
  -- 11. the leaf's equality test
  have h35c : evalOperand (contP39S C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP39S_35 C s x inc nep ep v ix b35
  obtain ⟨s₁₁, hl₁₁, hs₁₁⟩ :=
    WalkLink.LeafBlock35_at (calls := stage2Calls stage2SubCalls) G (ContAC₆ C)
      (contP39S C s x inc nep ep v ix b35) hl₁₀'.inv' rfl h35c
  have hl₁₁' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₆ C)
      (contP39S C s x inc nep ep v ix b35) (ContAC₇ C)
      (contP35S C s x inc nep ep v ix b35) := by
    have harm : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by
      rw [hbne13]; rfl
    have hst : s₁₁ = contP35S C s x inc nep ep v ix b35 := by rw [hs₁₁, harm]; rfl
    rw [hst] at hl₁₁
    rw [harm] at hl₁₁
    exact hl₁₁
  -- 12. the token's end
  have hcond35 : evalOperand (contP35S C s x inc nep ep v ix b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    simp only [evalOperand]
    exact contP35S_cond C s x inc nep ep v ix b35
  obtain ⟨s₁₂, hl₁₂, hs₁₂⟩ :=
    WalkLink.if_end372_i_at (calls := stage2Calls stage2SubCalls) (G := G) (C := ContAC₇ C)
      (s := contP35S C s x inc nep ep v ix b35) hl₁₁'.inv' rfl (p := "LeafBlock35") rfl
      contPhiSeam hcond35 hend h8end hbit
  have hl₁₂' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₇ C)
      (contP35S C s x inc nep ep v ix b35) (ContSeamC C)
      (contSeamS C s x inc nep ep v ix b35 b8) := by
    rw [hs₁₂] at hl₁₂
    exact hl₁₂
  -- the head part, counted at twelve
  have hseg12 : Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamS C s x inc nep ep v ix b35 b8) 12 :=
    Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄' (Seg.tail hl₅' (Seg.tail hl₆' (Seg.tail hl₇' (Seg.tail hl₈' (Seg.tail hl₉' (Seg.tail hl₁₀' (Seg.tail hl₁₁' (Seg.tail hl₁₂' (Seg.nil hl₁₂'.inv'))))))))))))
  -- the class-C span
  have hC : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contSeamS C s x inc nep ep v ix b35 b8) (ContTailStartC C)
      (contTailStart C s x inc nep ep v ix b35 b8 x1) 5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contSeamS C s x inc nep ep v ix b35 b8) hl₁₂'.inv' rfl h8c hc110 hc116 hceq116
  -- the scan's three links, at the latch
  obtain ⟨s₁₃, hs₁₃, hscan⟩ :=
    walkScanLinks457 (calls := stage2Calls stage2SubCalls) (G := G)
      (C := TailCarryScan (ContTailStartC C) ev)
      (s := contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
      hTail.inv' rfl hpreS hincS hopS h3S hpos hreadS hbsS hloc105 h47 hbit47 hws47
      hloc96 hlatch
  exact ⟨s₁₃, hs₁₃, (Seg.measure hseg12).trans ((Seg.measure hC).trans (hTail.trans hscan))⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontPrefixSeg
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cond_true345_i_at

end WalkScope
end LeanLLVM.Refinement
