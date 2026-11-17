/-
# The seam states' invariant, from the head chain

The tail producers state their three callees' rows at a *seam* — the block where the
head chain hands over to the tail — and each of them takes the invariant at that seam as
a parameter: `hInvT` in `hcontTail_of_calls` and in the last entry's
`hcontTail_of_calls`-shaped consumer, `hInvS` in `scContTail_of_calls`
(`JsonStage2WalkDispatchSegments`).  Those parameters are the one input a class's *arm*
owes beside its rows: the seam state is further along the walk than the head, so nothing
about it follows from `WalkInv` at the head alone.

This module produces the three, and each is the head chain's own `inv'`:

* `contTailStartInv_of_cleanup` — the continuing route's seam,
  `ContTailStartC`/`contTailStartF`, from `hcontSpan17_of_cleanup`'s `n ≤ 17` links (the
  head's `nH ≤ 12` and the class-C span's five);
* `scSeamInv_of_scalar` — the plain-value route's seam,
  `HeadC₄₁₃ (ContAC₇ C)`/`scSeamS`, from the scalar prefix's eight links, the byte's
  three pivots and the tag-true seam's one, composed here;
* `hlastTailInv_of_facts` — the last entry's seam, `TailStartC`/`hlastTail`, from
  `hlastTailSeg`'s sixteen links (the failing count test's six, the whitespace check's
  four, the byte's pivots, the token's end and the class-C span's five).

## What each seam costs, clause by clause

The links hand the invariant on one at a time, and the seam's own step is where the
state stops being the head's.  Two changes reach `WalkInv`, and exactly two:

* **The environment is extended.**  The seam's step binds its own cells (`%ee.1.i`,
  `%or.cond677.i`, `%37`, `%cmp376.i`, `%or.cond524.i` at `if.end372.i`, and the span's
  pivots), and every one of those names is outside `walkCarriedNames`, outside
  `%k.0.i249`, `%sp.i.0248`, the six pointer names and the static list.  So `regs`,
  `ptrs`, `iter`, `blockIndex`, `inc_reg`, `idx_reg` and `depth_reg` are the head's own
  values read through `cells`: `WalkRegs.cells_of`, `WalkPtrs.cells_of` and
  `WalkIter.bind`.  `%8` is **not** among the seam's binds — the token's end reads it,
  it does not write it — which is what keeps `iter.reg8` the head byte's.
* **The block changes**, and `events_le` is the clause that reads it:
  `C.events.length ≤ C.k + walkEmitC C.block`.  The loop head is outside
  `walkEmitBlocks`, so its allowance is `0` (`walkEmitC_of_not_contains`) and
  `WalkInv.events_le_of_tight` gives the trace's count at the entries consumed; every
  block of the three chains — the head's pivots, the span's leaves, `if.end372.i`,
  `if.then413.i`, `z_arena_reserve.exit`'s callers and the last entry's counterparts —
  is likewise outside `walkEmitBlocks`, so the seam's allowance is `0` too and the
  inequality is the same `Nat` fact.  A seam *inside* the stretch would need the
  allowance's `1`; none of these three is, and that is why the phase argument is one
  `omega` rather than a walk over the chain's edges.

The rest of the fields are the invariant's own, read at a memory the chain changed in one
place: `if.end372.i` stores the token's end (`%end.i`) at `%t352.i + 8`.  That store is
the link's, and it is inside the token's staged extent, so `WalkInv.owned` only gains
cells, `frame` stays silent, and the two stack byte maps, the log's six words and the
event stream's bytes are separated from it (`stack_tok_sep`, `tok_z_sep`, `tok_ev_sep`,
`walkReadBytes_rootSlot_at`).  The two steps after it — the class-C span's pivots and
`HeadS413` — bind cells and nothing else, which is why the seam itself is an environment
extension: no store, no allocation, so `next_ge` and every memory clause are the link's
already.

## Why the invariant is not an invariant consequence at the head

`WalkInv G C s` at the head says nothing about the seam's *position* in the trace: the
head is `NodeBlock21` with `%8` the entry's first byte, and the seam is three to sixteen
links later with a different block, a longer environment and a written token record.  A
theorem that took only the head invariant would have to be true at every state that
carries it, and the seam state is not one of them — hence the chains: each link is the
machine's own step, and the invariant at its endpoint is the step's `inv'`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupSpan
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarOfStaging
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The high-byte route's seam -/

/-- **The invariant at the continuing route's tail start**, from the class's chain.  The
`n ≤ 17` links are `hcontSpan17_of_cleanup`'s (the head's `nH ≤ 12` and the class-C span's
five), and the seam they end at is the tail producers' `hInvT`.  The class's head inputs
are the bundle's, so a producer of the class hands its own fields and reads the invariant
here instead of taking it as a parameter. -/
theorem contTailStartInv_of_cleanup {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    WalkInv G (ContTailStartC C) (contTailStartF f) := by
  obtain ⟨n, _hn, hseg⟩ := hcontSpan17_of_cleanup (G := G) (C := C) (s := s) hInv hblock f
  exact hseg.inv'

/-! ### The plain-value route's seam -/

/-- **The invariant at the plain-value route's tail start, from the prefix's cells.**
`scSeamS` is the tag test's `1` arm at `if.end372.i`; the chain to it is the scalar prefix's
eight links (`scPrefixLand`), the byte's three pivots with no whitespace run (`scWsLeafSeg`)
and the seam's own step (`scSeamSeg`), and their composition's `inv'` is the `hInvS` the tail
producer reads.  The two cells the seam step needs are the prefix's: `%8` is the head's
byte (`sP35_env8`) and `%end.i` is the static row (`sP35_envEnd`, `WalkInv.regs`). -/
theorem scSeamInv_of_cells {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HcontScalarPrefix G C s) :
    WalkInv G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) := by
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₈ C)
      (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 8 :=
    scPrefixLand (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.h44 f.h58 f.hne44
      f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt f.hread35
  have hseg3 : Seg (stage2Calls stage2SubCalls) G (Scc₈ C)
      (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (Scc₁₁ C)
      (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 3 :=
    scWsLeafSeg (G := G) (C := C) (s := s) f.x f.inc f.nep f.ep f.v f.ix f.b35 hseg8.inv'
      f.hb13 f.hb32 f.hbne32
  have h8p : lookupName (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env "%8" =
      some (.int 8 f.x) := by
    rw [sP35_env8]; exact f.h8
  have hendp : lookupName (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) := by
    rw [sP35_envEnd]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have hseg1 : Seg (stage2Calls stage2SubCalls) G (Scc₁₁ C)
      (sP35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (Scc₁₂ C)
      (scSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 1 :=
    scSeamSeg (G := G) (C := C) (s := s) f.x f.inc f.nep f.ep f.v f.ix f.b35
      (Seg.measure hseg3).inv' h8p hendp f.hbit
  have hseg12 : WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₁₂ C)
      (scSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 12 :=
    hseg8.trans ((Seg.measure hseg3).trans (Seg.measure hseg1))
  have hcarry : Scc₁₂ C = HeadC₄₁₃ (ContAC₇ C) := rfl
  rw [hcarry] at hseg12
  exact hseg12.inv'

/-- **The invariant at the plain-value route's tail start, from the bundle.**  The bundle
above its tail is the prefix, so this is `scSeamInv_of_cells` at the bundle's own fields. -/
theorem scSeamInv_of_scalar {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HcontScalarFacts G C s) :
    WalkInv G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) :=
  scSeamInv_of_cells hInv hblock
    { x := f.x, h8 := f.h8, hlt91 := f.hlt91, h44 := f.h44, h58 := f.h58, hne44 := f.hne44,
      hbit := f.hbit, inc := f.inc, nep := f.nep, hinc := f.hinc, hnep := f.hnep,
      hnext := f.hnext, ep := f.ep, v := f.v, h5 := f.h5, hi63 := f.hi63, hread := f.hread,
      ix := f.ix, hidx5 := f.hidx5, htok5 := f.htok5, hgap5 := f.hgap5, hugt := f.hugt,
      b35 := f.b35, hread35 := f.hread35, hb13 := f.hb13, hb32 := f.hb32,
      hbne32 := f.hbne32 }

/-! ### The last entry's seam -/

/-- **The invariant at the last entry's tail start, at the byte's route.**
`hlastTailSegByte`'s `12 + hlastByteCount hb` links end at `TailStartC`/
`hlastTailByte`, which is the last entry's tail producer's `hInvT`; the bundle's fields are
the chain's inputs, so this is the head invariant plus the document's route, and not a new
premise. -/
theorem hlastTailInv_of_facts {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HlastFacts G C s) :
    WalkInv G (TailStartC C)
      (hlastTailByte C s f.x f.inc f.nep f.v f.ix f.b35 f.hb) := by
  have hhead : C.block = "NodeBlock21" := by
    rw [hblock]; rfl
  exact (hlastTailSegByte (G := G) (C := C) (s := s) hInv hhead f.h8 f.hlt91 f.hlt123
    f.hlt125 f.hne125 f.hinc f.hnep f.hge f.hav5 f.hidx5 f.htok5 f.hgap5 f.hugt
    f.hread35 f.hv63 f.hb f.hbit6 f.hc110 f.hc116 f.hceq116).inv'

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contTailStartInv_of_cleanup
#print axioms LeanLLVM.Refinement.WalkScope.scSeamInv_of_cells
#print axioms LeanLLVM.Refinement.WalkScope.scSeamInv_of_scalar
#print axioms LeanLLVM.Refinement.WalkScope.hlastTailInv_of_facts

end WalkScope
end LeanLLVM.Refinement
