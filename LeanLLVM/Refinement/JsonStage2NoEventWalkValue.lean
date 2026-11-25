/-
The no-event walk's value class: the entry's scalar run, its tail skip, and the
route's price.

`NodeBlock5`'s value arm sends the head's byte to `scalar`, whose `phi` run takes
the head's own cells (`%inc.peel`, `%idxprom.peel`, `%3`, the four count and
stack words) and whose end test splits the entry cursor.  From `scalar` the route
reads the next entry's lane (`cond.true`) or the document's length (`cond.end`),
and `cond.end`'s extent test enters `land.lhs.true` at a word `cond` that is the
scalar run's right bound: the next entry's position when one remains, the
document's length at the last entry.  `land.lhs.true` seeds the byte probe at
`%b - 1 + cond`, and the scan below it stops at the first whitespace at or after
the entry's position, which is the scalar token's end (`%ee.1`).  The scan's
price is `12 + 5 * (cond - lane)` (`JsonStage2NoEventWalkScalar`), and the head's
dispatch (two or three links) plus the extent test (two or three) total at most
six, which is why the class's price is `18 + 5 * (cond - lane)`.

**The head's edge, not the loop's.**  `scalar`'s `phi` run has four incoming
edges: `scalar.loopexit`'s (the loop's continuation, which
`JsonStage2NoEventWalkClose` states as `scalar_denote`) and the three dispatch
leaves' (`LeafBlock`, `LeafBlock1`, `LeafBlock3`).  Only the leaves' edge takes
the head's read cells, and its frame cell is the head's `%frame.0.ph1402` rather
than the loop's constant `1`; `valueScalar_denote` is that edge and
`valueScalarCells` its cells.  A route that read the loop's edge here would read
an environment no head has.

**What this module proves, and what it does not.**  It proves the base cells'
projections at a head, the staging reads the class consumes (the document's bytes
and the entry stream's lanes at the head's own memory), the `scalar` block's
head-edge run with its end test's two arms, the `cond.true`/`cond.end` extent
test at the run's own bound, and the class's route from a head to the number and
literal entries with `ScalarSkip`'s scan and its price.  It does not prove the
number and literal arms below those entries (`num_fast_el1`'s body proof is
obstructed, and the literal chain's dispatch blocks are not modelled), the
`after_value` dispatch and the `value.outer.backedge` return, or the target
head's production; the class's continuing row (`Stage2NoEventWalkRow.cont`) needs
those, and they are not part of this module.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkSeed
import LeanLLVM.Refinement.JsonStage2NoEventWalkScalar
import LeanLLVM.Refinement.JsonStage2StringBodyMemory

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The base cells at a head

`Stage2NoEventWalkHead.baseLookups` binds every name of the entry chain's table;
these are the projections the value route reads: the document's base and length,
the entry stream's base and count, the cursor record's cell, and the two
`gep`s the scalar path derives. -/

theorem Stage2NoEventWalkHead.bLookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%b" = some (.ptr K.b) :=
  h.baseLookups "%b" (.ptr K.b) (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem Stage2NoEventWalkHead.nLookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
  h.baseLookups "%n" (.int 64 (BitVec.ofNat 64 K.n)) (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem Stage2NoEventWalkHead.nepLookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
  h.baseLookups "%nep" (.int 64 (BitVec.ofNat 64 K.nep)) (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem Stage2NoEventWalkHead.epLookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%ep" = some (.ptr K.ep) :=
  h.baseLookups "%ep" (.ptr K.ep) (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

theorem Stage2NoEventWalkHead.k219Lookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%k219" = some (.ptr (K.c + 32)) :=
  h.baseLookups "%k219" (.ptr (K.c + 32)) (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4])

theorem Stage2NoEventWalkHead.gep1068Lookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%invariant.gep1068" = some (.ptr (K.b - 1)) :=
  h.baseLookups "%invariant.gep1068" (.ptr (K.b - 1)) (by
    simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4])

/-- **The index cell at the head's value**, a projection of the read layer. -/
theorem Stage2NoEventWalkHead.incPeel {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
  obtain ⟨lane, byte, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
  exact hinc

/-- **The entry's index cell at the head's value.** -/
theorem Stage2NoEventWalkHead.idxPeel {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ lane, lookupName s.env "%idxprom.peel" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
  obtain ⟨lane, byte, -, -, -, -, -, hidx, -, -, -, -⟩ := h.laneRead
  exact ⟨lane, hidx⟩

/-- **The document's length is inside the read-past bound.**  The invariant's
`maxDoc` is the record's `stage2MaxDocument`, so the length fits the sign-extended
word the extent test reads. -/
theorem Stage2NoEventWalkInv.nLt63 {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) : K.n < 2 ^ 63 := by
  have := h.maxDoc
  simp only [stage2MaxDocument] at this
  omega

/-! ### The staging's reads at the head's memory

The document and the entry stream are outside the run's regions, so the head's
memory still carries the caller's bytes there.  Each proof below is the region
argument once: the document and the entry stream are two entries of the ABI list
and the run's regions are the scratch buffer, the four staged objects, and the
stack interval the watermark leaves below the base. -/

/-- The first and fourth entries of a region list are separated. -/
private theorem valueSep_first_fourth {a b c d : Nat × Nat} {rest : List (Nat × Nat)}
    (h : DisjointRegions ((a :: b :: c :: d :: []) ++ rest)) :
    a.1 + a.2 ≤ d.1 ∨ d.1 + d.2 ≤ a.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨h1, -⟩ := h
  rw [List.pairwise_cons] at h1
  exact h1.1 d (by simp)

/-- The second and fourth entries of a region list are separated. -/
private theorem valueSep_second_fourth {a b c d : Nat × Nat} {rest : List (Nat × Nat)}
    (h : DisjointRegions ((a :: b :: c :: d :: []) ++ rest)) :
    b.1 + b.2 ≤ d.1 ∨ d.1 + d.2 ≤ b.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨h1, -⟩ := h
  rw [List.pairwise_cons] at h1
  obtain ⟨-, h1⟩ := h1
  rw [List.pairwise_cons] at h1
  exact h1.1 d (by simp)

/-- **The document's bytes are outside the run's regions.** -/
theorem Stage2NoEventWalkInv.docOutside {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    ∀ j, j < K.n → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.b + j) := by
  intro j hj hin
  obtain ⟨r, hr, hlo, hhi⟩ := hin
  have hsep := h.separate
  simp only [stage2NoEventRegions] at hsep
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_cons.mp hr with hsc | hst
    · subst hsc
      rcases valueSep_first_fourth hsep with h' | h' <;> omega
    · have hdoc : (K.b, K.n + stage2ReadTail) ∈
          stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
            K.tokensOut K.valuesOut K.sumOut K.err := by
        simp [stage2NoEventRegions]
      rcases disjointRegions_against
        (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
          K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
        (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep hdoc r hst with h' | h'
      · omega
      · omega
  · have hle : K.b + (K.n + stage2ReadTail) ≤ K.next0 :=
      h.watermark (K.b, K.n + stage2ReadTail) (by simp [stage2NoEventRegions])
    have hr' : r = (K.next0, K.nextEnd - K.next0) := by
      simpa only [List.mem_singleton] using hr
    subst hr'
    simp only at hlo hhi
    omega

/-- **The entry stream's lanes are outside the run's regions.** -/
theorem Stage2NoEventWalkInv.entriesOutside {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    ∀ j, j < 4 * K.nep → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.ep + j) := by
  intro j hj hin
  obtain ⟨r, hr, hlo, hhi⟩ := hin
  have hsep := h.separate
  simp only [stage2NoEventRegions] at hsep
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_cons.mp hr with hsc | hst
    · subst hsc
      rcases valueSep_second_fourth hsep with h' | h' <;> omega
    · have hep : (K.ep, 4 * K.nep) ∈
          stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
            K.tokensOut K.valuesOut K.sumOut K.err := by
        simp [stage2NoEventRegions]
      rcases disjointRegions_against
        (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
          K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
        (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep hep r hst with h' | h'
      · omega
      · omega
  · have hle : K.ep + 4 * K.nep ≤ K.next0 :=
      h.watermark (K.ep, 4 * K.nep) (by simp [stage2NoEventRegions])
    have hr' : r = (K.next0, K.nextEnd - K.next0) := by
      simpa only [List.mem_singleton] using hr
    subst hr'
    simp only at hlo hhi
    omega

/-- **The document at the head's memory.** -/
theorem Stage2NoEventWalkInv.docAt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    readBytes s.mem K.b K.n = some K.bs :=
  h.readBytes_off (K := K) (a := K.b) (N := K.n) (bs := K.bs)
    (by intro j hj hin; exact h.docOutside j hj hin) h.doc

/-- **One document byte at the head's memory.** -/
theorem Stage2NoEventWalkInv.docByte {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {j : Nat} (hj : j < K.n) :
    readByte s.mem (K.b + j) = some (K.bs.getD j 0) :=
  readByte_of_readBytes h.docAt hj

/-- **The entry stream at the head's memory.** -/
theorem Stage2NoEventWalkInv.entriesAt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    readLanes32 s.mem K.ep K.nep = some K.ent :=
  h.readLanes_off (K := K) (a := K.ep) (k := K.nep) (l := K.ent)
    (by intro j hj hin; exact h.entriesOutside j hj hin) h.entries

/-- **The entry at an index, as its lane word.**  A successful lane read gives the
entry's position and the four bytes it was read from, at the head's own memory. -/
theorem Stage2NoEventWalkHead.laneAt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) {i : Nat}
    (hi : i < K.nep) :
    ∃ q bs, K.ent[i]? = some q ∧ q < 2 ^ 32 ∧
      readBytes s.mem (K.ep + 4 * i) 4 = some bs ∧ bytesToNat bs = q := by
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep)
    (n := K.nep) (l := K.ent) h.inv.entriesAt
  obtain ⟨q, bs, hq, hread, hval⟩ := hget i hi
  have hqlt : q < 2 ^ 32 := by
    have hinside := h.inv.inside q (List.mem_of_getElem? hq)
    have := h.inv.maxDoc
    simp only [stage2MaxDocument] at this
    omega
  exact ⟨q, bs, hq, hqlt, hread, hval⟩

/-! ### The `scalar` block at the head's edge

`scalar`'s seven `phi`s select, on the dispatch leaves' edge, the head's read
cells: `%inc.lcssa = %inc.peel`, `%idxprom.lcssa = %idxprom.peel`,
`%.lcssa = %3`, `%frame.0.lcssa1097 = %frame.0.ph1402`,
`%sp.0.lcssa1091.wide = %sp.0.ph1403`, `%terms.0.lcssa1079 = %terms.0.ph1407`
and `%tokens.0.lcssa1073 = %tokens.0.ph1408`.  The block then forms the byte's
address `%b + %idxprom.lcssa` and the end test
`%cmp436 = ult %inc.lcssa %nep`.  The loop's edge (`scalar.loopexit`) is
`JsonStage2NoEventWalkClose`'s `scalar_denote`; this is the leaves' edge. -/

/-- The head edge's `phi` values, frame included. -/
def valueScalarVs (inc idx : BitVec 64) (bv : BitVec 8) (fr : BitVec 8)
    (sp : BitVec 32) (terms tok : BitVec 64) : List (String × Value) :=
  [("%inc.lcssa", .int 64 inc),
   ("%idxprom.lcssa", .int 64 idx),
   ("%.lcssa", .int 8 bv),
   ("%frame.0.lcssa1097", .int 8 fr),
   ("%sp.0.lcssa1091.wide", .int 32 sp),
   ("%terms.0.lcssa1079", .int 64 terms),
   ("%tokens.0.lcssa1073", .int 64 tok)]

/-- The `scalar` cells after the head edge's run: the frame is the head's own
`phi` rather than the loop's constant. -/
abbrev valueScalarCells (env : Env) (inc idx : BitVec 64) (bv : BitVec 8)
    (fr : BitVec 8) (sp : BitVec 32) (terms tok nep : BitVec 64) (a : Nat) : Env :=
  ("%cmp436", Value.int 1 (evalICmp .ult inc nep)) ::
    ("%arrayidx6.le1046", Value.ptr a) ::
    ("%tokens.0.lcssa1073", Value.int 64 tok) ::
    ("%terms.0.lcssa1079", Value.int 64 terms) ::
    ("%sp.0.lcssa1091.wide", Value.int 32 sp) ::
    ("%frame.0.lcssa1097", Value.int 8 fr) ::
    ("%.lcssa", Value.int 8 bv) ::
    ("%idxprom.lcssa", Value.int 64 idx) ::
    ("%inc.lcssa", Value.int 64 inc) :: env

/-- **The `phi` run on the dispatch leaves' edge**: each member selects the
head's own cell at the leaf the state names. -/
theorem valueScalar_phiSelects (env : Env) (s : State) {pre : String}
    (hpre : s.pre = some pre)
    (hpre' : pre = "LeafBlock" ∨ pre = "LeafBlock1" ∨ pre = "LeafBlock3")
    {inc idx : BitVec 64} {bv : BitVec 8} {fr : BitVec 8} {sp : BitVec 32}
    {terms tok : BitVec 64}
    (hinc : lookupName env "%inc.peel" = some (.int 64 inc))
    (hidx : lookupName env "%idxprom.peel" = some (.int 64 idx))
    (hbv : lookupName env "%3" = some (.int 8 bv))
    (hfr : lookupName env "%frame.0.ph1402" = some (.int 8 fr))
    (hsp : lookupName env "%sp.0.ph1403" = some (.int 32 sp))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 tok)) :
    PhiSelects (stateAt env s) pre scalarPhiSpecs
      (valueScalarVs inc idx bv fr sp terms tok) := by
  rcases hpre' with rfl | rfl | rfl
  all_goals
    simp only [valueScalarVs]
    refine PhiSelects.cons (op := .reg "%inc.peel") (by decide) ?_
      (PhiSelects.cons (op := .reg "%idxprom.peel") (by decide) ?_
        (PhiSelects.cons (op := .reg "%3") (by decide) ?_
          (PhiSelects.cons (op := .reg "%frame.0.ph1402") (by decide) ?_
            (PhiSelects.cons (op := .reg "%sp.0.ph1403") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.0.ph1407") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.0.ph1408") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, hinc, hidx, hbv, hfr, hsp, htr, htok]

/-- **The `scalar` block on the dispatch leaves' edge.**  The `phi` run selects
the head's cells, and the block forms the entry byte's address and the end test.
The predecessor is one of the three leaves, so the selected operands are the
head's. -/
theorem valueScalar_denote {calls : Calls} (env : Env) (s : State)
    {pre : String} (hpre : s.pre = some pre)
    (hpre' : pre = "LeafBlock" ∨ pre = "LeafBlock1" ∨ pre = "LeafBlock3")
    {inc idx : BitVec 64} {bv : BitVec 8} {fr : BitVec 8} {sp : BitVec 32}
    {terms tok nep : BitVec 64} {b : Nat}
    (hinc : lookupName env "%inc.peel" = some (.int 64 inc))
    (hidx : lookupName env "%idxprom.peel" = some (.int 64 idx))
    (hbv : lookupName env "%3" = some (.int 8 bv))
    (hfr : lookupName env "%frame.0.ph1402" = some (.int 8 fr))
    (hsp : lookupName env "%sp.0.ph1403" = some (.int 32 sp))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 tok))
    (hb : lookupName env "%b" = some (.ptr b))
    (hnep : lookupName env "%nep" = some (.int 64 nep))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    denoteCode calls scalarInstrs (stateAt env s) =
      some (stateAt (valueScalarCells env inc idx bv fr sp terms tok nep
        (b + (idx.signExtend 64).toNat)) s) := by
  have hsel := valueScalar_phiSelects env s hpre hpre' hinc hidx hbv hfr hsp htr htok
  rw [scalarPhi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := pre) (specs := scalarPhiSpecs)
      (vs := valueScalarVs inc idx bv fr sp terms tok)
      (rest := [Instr.gep "%arrayidx6.le1046" (Ty.int 8) (Operand.reg "%b")
          (Operand.reg "%idxprom.lcssa"),
        Instr.icmp "%cmp436" IPred.ult 64 (Operand.reg "%inc.lcssa")
          (Operand.reg "%nep")])
      (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  have hB : lookupName (runCells (valueScalarVs inc idx bv fr sp terms tok) env) "%b"
      = some (.ptr b) := by
    simp only [valueScalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hNep : lookupName (runCells (valueScalarVs inc idx bv fr sp terms tok) env) "%nep"
      = some (.int 64 nep) := by
    simp only [valueScalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hIdxCell : lookupName (runCells (valueScalarVs inc idx bv fr sp terms tok) env)
      "%idxprom.lcssa" = some (.int 64 idx) := by
    simp only [valueScalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hIncCell : lookupName (runCells (valueScalarVs inc idx bv fr sp terms tok) env)
      "%inc.lcssa" = some (.int 64 inc) := by
    simp only [valueScalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := runCells (valueScalarVs inc idx bv fr sp terms tok) env) (s := s)
    (d := "%arrayidx6.le1046") (base := "%b") (off := "%idxprom.lcssa")
    (a := b) (idx := idx) hB hIdxCell hpos]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%arrayidx6.le1046", .ptr (b + (idx.signExtend 64).toNat)) ::
      runCells (valueScalarVs inc idx bv fr sp terms tok) env) (s := s)
    (d := "%cmp436") (a := "%inc.lcssa") (b := "%nep") (p := .ult) (w := 64)
    (x := inc) (y := nep)
    (lookupName_cons_other _ _ _ (by decide) hIncCell)
    (lookupName_cons_other _ _ _ (by decide) hNep) (is := [])]
  simp only [denoteCode_nil, valueScalarCells, valueScalarVs, runCells]

/-! ### The end test's two arms -/

/-- **The head edge's end test, taken**: the cursor is below the entry count, to
`cond.true`. -/
theorem link_valueScalar_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {pre : String} {inc idx : BitVec 64} {bv : BitVec 8}
    {fr : BitVec 8} {sp : BitVec 32} {terms tok nep : BitVec 64} {b : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar")
    (hpre : s.pre = some pre)
    (hpre' : pre = "LeafBlock" ∨ pre = "LeafBlock1" ∨ pre = "LeafBlock3")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.peel" = some (.int 64 idx))
    (hbv : lookupName s.env "%3" = some (.int 8 bv))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 fr))
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hy : evalICmp .ult inc nep = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (valueScalarCells s.env inc idx bv fr sp terms tok nep
          (b + (idx.signExtend 64).toNat)) s "cond.true") := by
  have hblock : scalarBlock.instrs = scalarInstrs := by decide
  have hcode : denoteCode calls scalarBlock.instrs (stateAt s.env s) =
      some (stateAt
        (valueScalarCells s.env inc idx bv fr sp terms tok nep
          (b + (idx.signExtend 64).toNat)) s) := by
    rw [hblock]
    exact valueScalar_denote (calls := calls) s.env s hpre hpre'
      hinc hidx hbv hfr hsp htr htok hb hnep hpos
  exact stage2NoEventWalkLink_condbr_true
    (env' := valueScalarCells s.env inc idx bv fr sp terms tok nep
      (b + (idx.signExtend 64).toNat))
    h (by rw [hpc]; exact scalarBlock_find) hcode rfl
    (by simp only [valueScalarCells, lookupName_cons_self, hy])

/-- **The head edge's end test, not taken**: the entry cursor has reached the
entry count, to `cond.end`. -/
theorem link_valueScalar_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {pre : String} {inc idx : BitVec 64} {bv : BitVec 8}
    {fr : BitVec 8} {sp : BitVec 32} {terms tok nep : BitVec 64} {b : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar")
    (hpre : s.pre = some pre)
    (hpre' : pre = "LeafBlock" ∨ pre = "LeafBlock1" ∨ pre = "LeafBlock3")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.peel" = some (.int 64 idx))
    (hbv : lookupName s.env "%3" = some (.int 8 bv))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 fr))
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hy : evalICmp .ult inc nep = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (valueScalarCells s.env inc idx bv fr sp terms tok nep
          (b + (idx.signExtend 64).toNat)) s "cond.end") := by
  have hblock : scalarBlock.instrs = scalarInstrs := by decide
  have hcode : denoteCode calls scalarBlock.instrs (stateAt s.env s) =
      some (stateAt
        (valueScalarCells s.env inc idx bv fr sp terms tok nep
          (b + (idx.signExtend 64).toNat)) s) := by
    rw [hblock]
    exact valueScalar_denote (calls := calls) s.env s hpre hpre'
      hinc hidx hbv hfr hsp htr htok hb hnep hpos
  exact stage2NoEventWalkLink_condbr_false
    (env' := valueScalarCells s.env inc idx bv fr sp terms tok nep
      (b + (idx.signExtend 64).toNat))
    h (by rw [hpc]; exact scalarBlock_find) hcode rfl
    (by simp only [valueScalarCells, lookupName_cons_self, hy])

/-! ### The route from a scalar state to the number and literal entries

`JsonStage2NoEventWalkScalar`'s `stage2NoEventWalkScalarSkip` starts at
`land.lhs.true`.  This section brings the walk there from the `scalar` block's
head-edge state and applies the scan, once per arm of the end test:

* the entry cursor is below the entry count: `cond.true` reads the next entry's
  lane word, and the extent test takes it against the current entry's position
  because the stream is strictly increasing;
* the cursor has reached the entry count: `%cond` is the document's length, and
  the extent test takes it because every entry starts inside the document.

Either way the bound `cond` is at least one and at most the document's length, so
the scan's probe and its bytes are the document's, and its price is
`12 + 5 * (cond - lane)` on top of the two or three links.  The scan reports the
bound it stopped at and the non-membership it passed: on the loop arm every
position in `[lane, q)` is not whitespace, and on the direct arm the probe's byte
at `%b - 1 + cond` is not whitespace at `q = cond`. -/


/-- A strictly increasing list of document positions is no longer than the
document.  Each step rises by at least one, so the position at an index is at
least the index, and the last one is inside the document. -/
theorem valueEnt_length_le {l : List Nat} (h : l.Pairwise (· < ·)) {n : Nat}
    (hin : ∀ x ∈ l, x < n) : l.length ≤ n := by
  cases l with
  | nil => exact Nat.zero_le n
  | cons a rest =>
      have hge : ∀ (i : Nat) (hi : i < (a :: rest).length), i ≤ (a :: rest)[i] := by
        intro i
        induction i with
        | zero => intro _; exact Nat.zero_le _
        | succ i ih =>
            intro hi
            have hi' : i < (a :: rest).length := by
              simp only [List.length_cons] at hi ⊢; omega
            have hlt := (List.pairwise_iff_getElem.mp h) i (i + 1) hi' hi (by omega)
            have h1 := ih hi'
            omega
      have hlen : 0 < (a :: rest).length := by simp only [List.length_cons]; omega
      have hlast : (a :: rest).length - 1 ≤ (a :: rest)[(a :: rest).length - 1] :=
        hge _ (by omega)
      have hltn : (a :: rest)[(a :: rest).length - 1] < n :=
        hin _ (List.getElem_mem (by omega))
      omega

/-- **The entry count does not exceed the document's length.**  The entries are
strictly increasing positions, each inside the document. -/
theorem Stage2NoEventWalkInv.nepLe {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) : K.nep ≤ K.n := by
  have hlen : K.ent.length = K.nep := readLanes32_length mem K.ep K.nep K.ent h.entries
  rw [← hlen]
  exact valueEnt_length_le h.order h.inside

/-- `ult` at one, from the `Nat` order. -/
theorem value_ult_one {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a < b) :
    evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  have htoNat : (BitVec.ofNat 64 a).toNat < (BitVec.ofNat 64 b).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact h
  have hult : BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true :=
    BitVec.ult_iff_toNat_lt.mpr htoNat
  show BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) = 1
  rw [hult]
  rfl

/-- `ult` at zero, from the `Nat` order. -/
theorem value_ult_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ¬ a < b) :
    evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0 := by
  have htoNat : ¬ (BitVec.ofNat 64 a).toNat < (BitVec.ofNat 64 b).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact h
  have hult : BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
    cases h' : BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
    · rfl
    · rw [BitVec.ult_iff_toNat_lt] at h'
      exact absurd h' htoNat
  show BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) = 0
  rw [hult]
  rfl

/-- `ugt` at one, from the `Nat` order. -/
theorem value_ugt_one {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : b < a) :
    evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  have htoNat : (BitVec.ofNat 64 b).toNat < (BitVec.ofNat 64 a).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact h
  have hult : BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = true :=
    BitVec.ult_iff_toNat_lt.mpr htoNat
  show BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a)) = 1
  rw [hult]
  rfl

/-- The sign-extension of a lane position is itself. -/
theorem value_signExtend_lane {lane : Nat} (h : lane < 2 ^ 32) :
    ((BitVec.ofNat 64 lane).signExtend 64).toNat = lane := by
  rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The `scalar` block's cells at a head's values. -/
abbrev valueScalarEnv (env : Env) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) : Env :=
  valueScalarCells env (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 lane) bv
    (BitVec.ofNat 8 fr) (BitVec.ofNat 32 sp) (BitVec.ofNat 64 K.terms)
    (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.nep)
    (K.b + ((BitVec.ofNat 64 lane).signExtend 64).toNat)

/-- The `cond.true` cells at the next entry's lane read. -/
abbrev valueCondTrueEnv (env : Env) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) (bs : List UInt8) : Env :=
  condTrueCells (valueScalarEnv env k lane sp fr bv K)
    (K.ep + ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat * 4) bs

/-- The `cond.end` cells at the extent test's word. -/
abbrev valueLandEnv (env : Env) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) (bs : List UInt8) (c : Nat) : Env :=
  condEndCells (valueCondTrueEnv env k lane sp fr bv K bs) (BitVec.ofNat 64 c)
    (BitVec.ofNat 64 lane)

/-- The `scalar` hand-off state at `cond.true`. -/
abbrev valueCondTrueState (e : State) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) : State :=
  stage2NoEventWalkNext (valueScalarEnv e.env k lane sp fr bv K) e "cond.true"

/-- The `cond.end` state at the next entry's lane read. -/
abbrev valueCondEndState (e : State) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) (bs : List UInt8) : State :=
  stage2NoEventWalkNext (valueCondTrueEnv e.env k lane sp fr bv K bs)
    (valueCondTrueState e k lane sp fr bv K) "cond.end"

/-- The `land.lhs.true` state at a taken extent test. -/
abbrev valueLandState (e : State) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) (bs : List UInt8) (c : Nat) : State :=
  stage2NoEventWalkNext (valueLandEnv e.env k lane sp fr bv K bs c)
    (valueCondEndState e k lane sp fr bv K bs) "land.lhs.true"

/-- The `cond.end` state at the document's length. -/
abbrev valueCondEndStateZ (e : State) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) : State :=
  stage2NoEventWalkNext (valueScalarEnv e.env k lane sp fr bv K) e "cond.end"

/-- The `land.lhs.true` state at the document's length. -/
abbrev valueLandStateZ (e : State) (k lane sp fr : Nat) (bv : BitVec 8)
    (K : Stage2NoEventWalkCarry) : State :=
  stage2NoEventWalkNext
    (condEndCells (valueScalarEnv e.env k lane sp fr bv K) (BitVec.ofNat 64 K.n)
      (BitVec.ofNat 64 lane))
    (valueCondEndStateZ e k lane sp fr bv K) "land.lhs.true"

/-- **The value class's route from a scalar state.**  From the `scalar` block's
head-edge state — its seven `phi` cells, the entry's position and byte, and the
entry chain's two `gep`s — the walk reaches the number or literal entry with the
scan's `%ee.1` inside `[lane, cond]`, the invariant there, the scan's write, and a
run of at most `15 + 5 * (cond - lane)` steps, where `cond` is the next entry's
position or the document's length. -/
theorem stage2NoEventWalkValueAt {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {e : State} {pre : String} {k lane sp fr : Nat} {bv : BitVec 8}
    (hinv : Stage2NoEventWalkInv K mem e) (hpc : e.pc = "scalar")
    (hpre : e.pre = some pre)
    (hpre' : pre = "LeafBlock" ∨ pre = "LeafBlock1" ∨ pre = "LeafBlock3")
    (hb1 : 1 ≤ K.b)
    (hent : K.ent[k]? = some lane) (hlane32 : lane < 2 ^ 32)
    (hinc : lookupName e.env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hidx : lookupName e.env "%idxprom.peel" = some (.int 64 (BitVec.ofNat 64 lane)))
    (hbv : lookupName e.env "%3" = some (.int 8 bv))
    (hfr : lookupName e.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName e.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (htr : lookupName e.env "%terms.0.ph1407" = some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok : lookupName e.env "%tokens.0.ph1408" = some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hb : lookupName e.env "%b" = some (.ptr K.b))
    (hnep : lookupName e.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)))
    (hn : lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)))
    (hep : lookupName e.env "%ep" = some (.ptr K.ep))
    (hgep : lookupName e.env "%invariant.gep1068" = some (.ptr (K.b - 1)))
    (hk219 : lookupName e.env "%k219" = some (.ptr (K.c + 32)))
    (klt : k < K.nep) :
    ∃ (e' : State) (j q cond : Nat),
      j ≤ 15 + 5 * (cond - lane) ∧
      (e'.pc = "if.then471" ∨ e'.pc = "if.else495") ∧
      lookupName e'.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lane ≤ q ∧ q ≤ cond ∧ cond ≤ K.n ∧ lane < cond ∧
      (cond = K.n ∨ K.ent[k + 1]? = some cond) ∧
      (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD q 0).toNat) = true) ∧
      ((∀ j, lane ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (K.bs.getD j 0).toNat) = false) ∨
        (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD (cond - 1) 0).toNat) = false)) ∧
      Stage2NoEventWalkInv K mem e' ∧
      e'.mem = writeBytes e.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 1)).toNat 8) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody e =
        runFuel calls n stage2NoEventBody e') := by
  have hpos : ((BitVec.ofNat 64 lane).signExtend 64).toNat < 2 ^ 63 := by
    rw [value_signExtend_lane hlane32]; omega
  have hk1lt64 : k + 1 < 2 ^ 64 := by have := hinv.nepLt; omega
  have hincpos : ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat = k + 1 := by
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1lt64]
  have hpos' : ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [hincpos]
    have h1 := hinv.nepLe
    have h2 := hinv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hn64 : K.n < 2 ^ 64 := hinv.nLt
  by_cases hlt : k + 1 < K.nep
  · -- the cursor is below the entry count: the next entry's lane is the bound
    obtain ⟨-, hget⟩ := readLanes32_lane (m := e.mem) (addr := K.ep) (n := K.nep)
      (l := K.ent) hinv.entriesAt
    obtain ⟨q, bs4, hentq, hread4, hbs4⟩ := hget (k + 1) hlt
    have hqlt : q < K.n := hinv.inside q (List.mem_of_getElem? hentq)
    have hq32 : q < 2 ^ 32 := by
      have := hinv.maxDoc; simp only [stage2MaxDocument] at this; omega
    have hq64 : q < 2 ^ 64 := by omega
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hent
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hentq
    have hord : lane < q := by
      have h := (List.pairwise_iff_getElem.mp hinv.order) k (k + 1) hkltL hqltL (by omega)
      rw [hkval, hqval] at h
      exact h
    have hy1 : evalICmp .ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = 1 :=
      value_ult_one hk1lt64 hinv.nepLt hlt
    have hload4 : readBytes e.mem (K.ep + ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat
        * 4) 4 = some bs4 := by
      rw [hincpos, Nat.mul_comm]
      exact hread4
    -- the three links
    have L1 := link_valueScalar_true (calls := calls) (K := K) (mem := mem)
      (pre := pre) (inc := BitVec.ofNat 64 (k + 1)) (idx := BitVec.ofNat 64 lane)
      (bv := bv) (fr := BitVec.ofNat 8 fr) (sp := BitVec.ofNat 32 sp)
      (terms := BitVec.ofNat 64 K.terms) (tok := BitVec.ofNat 64 K.tok)
      (nep := BitVec.ofNat 64 K.nep) (b := K.b)
      hinv hpc hpre hpre' hinc hidx hbv hfr hsp htr htok hb hnep hpos hy1
    have hep1 : lookupName (valueScalarEnv e.env k lane sp fr bv K) "%ep"
        = some (.ptr K.ep) := by
      simp only [valueScalarEnv, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hep
    have hinc1 : lookupName (valueScalarEnv e.env k lane sp fr bv K) "%inc.lcssa"
        = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
      simp only [valueScalarEnv, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have L2 := link_condTrue (calls := calls) (K := K) (mem := mem) (ep := K.ep)
      (inc := BitVec.ofNat 64 (k + 1)) (bs := bs4)
      L1.inv' rfl
      (by simpa only [valueCondTrueState, valueScalarEnv, stage2NoEventWalkNext] using hep1)
      (by simpa only [valueCondTrueState, valueScalarEnv, stage2NoEventWalkNext] using hinc1)
      hpos' hload4
    have hconv2 : lookupName (valueCondTrueEnv e.env k lane sp fr bv K bs4) "%conv439"
        = some (.int 64 (BitVec.ofNat 64 q)) := by
      have hq32' : (BitVec.ofNat 32 q).toNat = q := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [valueCondTrueEnv, condTrueCells, hbs4, hq32']
      rw [lookupName_cons_self]
    have hidx2 : lookupName (valueCondTrueEnv e.env k lane sp fr bv K bs4) "%idxprom.lcssa"
        = some (.int 64 (BitVec.ofNat 64 lane)) := by
      simp only [valueCondTrueEnv, condTrueCells, valueScalarEnv, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hy2 : evalICmp .ugt (BitVec.ofNat 64 q) (BitVec.ofNat 64 lane) = 1 :=
      value_ugt_one hq64 (by omega) hord
    have L3 := link_condEnd_fromCondTrue_true (calls := calls) (K := K) (mem := mem)
      (c := BitVec.ofNat 64 q) (idx := BitVec.ofNat 64 lane)
      L2.inv' rfl rfl
      (by simpa only [valueCondEndState, valueCondTrueEnv, valueScalarEnv, stage2NoEventWalkNext] using hconv2)
      (by simpa only [valueCondEndState, valueCondTrueEnv, valueScalarEnv, stage2NoEventWalkNext] using hidx2)
      hy2
    have hcL : lookupName (valueLandState e k lane sp fr bv K bs4 q).env "%cond"
        = some (.int 64 (BitVec.ofNat 64 q)) := by
      simp only [valueLandState, valueLandEnv, stage2NoEventWalkNext, condEndCells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hidxL : lookupName (valueLandState e k lane sp fr bv K bs4 q).env
        "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)) := by
      simp only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
        stage2NoEventWalkNext, condEndCells, condTrueCells, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hincL : lookupName (valueLandState e k lane sp fr bv K bs4 q).env "%inc.lcssa"
        = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
      simp only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
        stage2NoEventWalkNext, condEndCells, condTrueCells, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hlcL : lookupName (valueLandState e k lane sp fr bv K bs4 q).env "%.lcssa"
        = some (.int 8 bv) := by
      simp only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
        stage2NoEventWalkNext, condEndCells, condTrueCells, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hbL : lookupName (valueLandState e k lane sp fr bv K bs4 q).env "%b"
        = some (.ptr K.b) := by
      simp only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
        stage2NoEventWalkNext, condEndCells, condTrueCells, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hb
    have hgepL : lookupName (valueLandState e k lane sp fr bv K bs4 q).env
        "%invariant.gep1068" = some (.ptr (K.b - 1)) := by
      simp only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
        stage2NoEventWalkNext, condEndCells, condTrueCells, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hgep
    have hk219L : lookupName (valueLandState e k lane sp fr bv K bs4 q).env "%k219"
        = some (.ptr (K.c + 32)) := by
      simp only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
        stage2NoEventWalkNext, condEndCells, condTrueCells, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hk219
    have hqpos : 1 ≤ q := by omega
    have hread0 : readByte (valueLandState e k lane sp fr bv K bs4 q).mem
        ((K.b - 1) + q) = some (K.bs.getD (q - 1) 0) := by
      have haddr : (K.b - 1) + q = K.b + (q - 1) := by omega
      have hmem : (valueLandState e k lane sp fr bv K bs4 q).mem = e.mem := rfl
      rw [hmem, haddr]
      exact hinv.docByte (by omega)
    have hbytes : ∀ j, j < q → readByte (valueLandState e k lane sp fr bv K bs4 q).mem
        (K.b + j) = some (K.bs.getD j 0) := by
      intro j hj
      have hmem : (valueLandState e k lane sp fr bv K bs4 q).mem = e.mem := rfl
      rw [hmem]
      exact hinv.docByte (by omega)
    have hpcL : (valueLandState e k lane sp fr bv K bs4 q).pc = "land.lhs.true" := rfl
    have hcondlt : q < 2 ^ 63 := by omega
    obtain ⟨e', jS, q', hjS, hpc', hee, hq1, hq2, hws, hprefix, hinv', hmem', hrun'⟩ :=
      stage2NoEventWalkScalarSkip (calls := calls) (K := K) (mem := mem)
        (s := valueLandState e k lane sp fr bv K bs4 q)
        (g := K.b - 1) (b := K.b) (idx := lane) (cond := q)
        (σ := fun j => K.bs.getD j 0) (u0 := K.bs.getD (q - 1) 0)
        (inc := BitVec.ofNat 64 (k + 1)) (lc := bv) (k219 := K.c + 32)
        (by simpa only [valueLandState, valueLandEnv, valueCondTrueEnv, valueScalarEnv,
          stage2NoEventWalkNext] using L3.inv')
        hpcL hgepL hcL hidxL hbL hincL hlcL hk219L rfl hread0 hbytes hord hcondlt
    have hrunHL : ∀ n, runFuel calls (3 + n) stage2NoEventBody e =
        runFuel calls n stage2NoEventBody (valueLandState e k lane sp fr bv K bs4 q) := by
      intro n
      rw [show 3 + n = 1 + (1 + (1 + n)) from by omega,
        stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
        stage2NoEventWalkLink_runFuel L3]
      rfl
    refine ⟨e', 3 + jS, q', q, ?_, hpc', hee, ?_, hq2, ?_, hord, ?_, hws, hprefix,
      hinv', ?_, ?_⟩
    · omega
    · omega
    · omega
    · exact Or.inr hentq
    · exact hmem'
    · intro n
      rw [show 3 + jS + n = 3 + (jS + n) from by omega, hrunHL (jS + n), hrun' n]
  · -- the cursor has reached the entry count: the document's length is the bound
    have hlaneN : lane < K.n := hinv.inside lane (List.mem_of_getElem? hent)
    have hy0 : evalICmp .ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = 0 :=
      value_ult_zero hk1lt64 hinv.nepLt (by omega)
    have hyq : evalICmp .ugt (BitVec.ofNat 64 K.n) (BitVec.ofNat 64 lane) = 1 :=
      value_ugt_one hn64 (by omega) hlaneN
    have L1 := link_valueScalar_false (calls := calls) (K := K) (mem := mem)
      (pre := pre) (inc := BitVec.ofNat 64 (k + 1)) (idx := BitVec.ofNat 64 lane)
      (bv := bv) (fr := BitVec.ofNat 8 fr) (sp := BitVec.ofNat 32 sp)
      (terms := BitVec.ofNat 64 K.terms) (tok := BitVec.ofNat 64 K.tok)
      (nep := BitVec.ofNat 64 K.nep) (b := K.b)
      hinv hpc hpre hpre' hinc hidx hbv hfr hsp htr htok hb hnep hpos hy0
    have hn1 : lookupName (valueScalarEnv e.env k lane sp fr bv K) "%n"
        = some (.int 64 (BitVec.ofNat 64 K.n)) := by
      simp only [valueScalarEnv, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hn
    have hidx1 : lookupName (valueScalarEnv e.env k lane sp fr bv K) "%idxprom.lcssa"
        = some (.int 64 (BitVec.ofNat 64 lane)) := by
      simp only [valueScalarEnv, valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have L2 := link_condEnd_true (calls := calls) (K := K) (mem := mem)
      (c := BitVec.ofNat 64 K.n) (idx := BitVec.ofNat 64 lane)
      L1.inv' rfl
      (by simp only [stage2NoEventWalkNext]; rw [hpc])
      (by simpa only [valueCondEndStateZ, valueScalarEnv, stage2NoEventWalkNext] using hn1)
      (by simpa only [valueCondEndStateZ, valueScalarEnv, stage2NoEventWalkNext] using hidx1)
      hyq
    have hcZ : lookupName (valueLandStateZ e k lane sp fr bv K).env "%cond"
        = some (.int 64 (BitVec.ofNat 64 K.n)) := by
      simp only [valueLandStateZ, stage2NoEventWalkNext, condEndCells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hidxZ : lookupName (valueLandStateZ e k lane sp fr bv K).env "%idxprom.lcssa"
        = some (.int 64 (BitVec.ofNat 64 lane)) := by
      simp only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext, condEndCells,
        valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hincZ : lookupName (valueLandStateZ e k lane sp fr bv K).env "%inc.lcssa"
        = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
      simp only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext, condEndCells,
        valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hlcZ : lookupName (valueLandStateZ e k lane sp fr bv K).env "%.lcssa"
        = some (.int 8 bv) := by
      simp only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext, condEndCells,
        valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
    have hbZ : lookupName (valueLandStateZ e k lane sp fr bv K).env "%b"
        = some (.ptr K.b) := by
      simp only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext, condEndCells,
        valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hb
    have hgepZ : lookupName (valueLandStateZ e k lane sp fr bv K).env
        "%invariant.gep1068" = some (.ptr (K.b - 1)) := by
      simp only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext, condEndCells,
        valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hgep
    have hk219Z : lookupName (valueLandStateZ e k lane sp fr bv K).env "%k219"
        = some (.ptr (K.c + 32)) := by
      simp only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext, condEndCells,
        valueScalarCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hk219
    have hread0 : readByte (valueLandStateZ e k lane sp fr bv K).mem ((K.b - 1) + K.n)
        = some (K.bs.getD (K.n - 1) 0) := by
      have haddr : (K.b - 1) + K.n = K.b + (K.n - 1) := by omega
      have hmem : (valueLandStateZ e k lane sp fr bv K).mem = e.mem := rfl
      rw [hmem, haddr]
      exact hinv.docByte (by omega)
    have hbytes : ∀ j, j < K.n → readByte (valueLandStateZ e k lane sp fr bv K).mem
        (K.b + j) = some (K.bs.getD j 0) := by
      intro j hj
      have hmem : (valueLandStateZ e k lane sp fr bv K).mem = e.mem := rfl
      rw [hmem]
      exact hinv.docByte hj
    have hpcZ : (valueLandStateZ e k lane sp fr bv K).pc = "land.lhs.true" := rfl
    obtain ⟨e', jS, q', hjS, hpc', hee, hq1, hq2, hws, hprefix, hinv', hmem', hrun'⟩ :=
      stage2NoEventWalkScalarSkip (calls := calls) (K := K) (mem := mem)
        (s := valueLandStateZ e k lane sp fr bv K)
        (g := K.b - 1) (b := K.b) (idx := lane) (cond := K.n)
        (σ := fun j => K.bs.getD j 0) (u0 := K.bs.getD (K.n - 1) 0)
        (inc := BitVec.ofNat 64 (k + 1)) (lc := bv) (k219 := K.c + 32)
        (by simpa only [valueLandStateZ, valueScalarEnv, stage2NoEventWalkNext] using L2.inv')
        hpcZ hgepZ hcZ hidxZ hbZ hincZ hlcZ hk219Z rfl hread0 hbytes hlaneN
        hinv.nLt63
    have hrunHL : ∀ n, runFuel calls (2 + n) stage2NoEventBody e =
        runFuel calls n stage2NoEventBody (valueLandStateZ e k lane sp fr bv K) := by
      intro n
      rw [show 2 + n = 1 + (1 + n) from by omega,
        stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2]
      rfl
    refine ⟨e', 2 + jS, q', K.n, ?_, hpc', hee, ?_, hq2, le_rfl, hlaneN, ?_, hws,
      hprefix, hinv', ?_, ?_⟩
    · omega
    · omega
    · exact Or.inl rfl
    · exact hmem'
    · intro n
      rw [show 2 + jS + n = 2 + (jS + n) from by omega, hrunHL (jS + n), hrun' n]

/-! ### The head's dispatch to `scalar`

`NodeBlock5`'s three leaves send any byte other than `"`, `[` and `{` to
`scalar`.  The dispatch is two links on `LeafBlock`'s path and three on
`LeafBlock1`'s and `LeafBlock3`'s, and the target's environment is the head's
behind the leaf's own two or three cells.  This section states the three paths
with their run counts, then the `scalar` state's register bundle at a head's
values, which is what the class's route consumes. -/

/-- The hand-off state's memory is its source's. -/
@[simp] theorem stage2NoEventWalkNext_mem (env : Env) (s : State) (pc : String) :
    (stage2NoEventWalkNext env s pc).mem = s.mem := rfl

/-- The hand-off state's `pc` is the block it names. -/
@[simp] theorem stage2NoEventWalkNext_pc (env : Env) (s : State) (pc : String) :
    (stage2NoEventWalkNext env s pc).pc = pc := rfl

/-- The hand-off state's predecessor is its source's `pc`. -/
@[simp] theorem stage2NoEventWalkNext_pre (env : Env) (s : State) (pc : String) :
    (stage2NoEventWalkNext env s pc).pre = some s.pc := rfl

/-- The register bundle a `scalar` state carries at a head's values: the seven
`phi` inputs, the entry chain's base cells the route reads, and the entry's lane
and byte. -/
structure Stage2NoEventWalkValueRegs (K : Stage2NoEventWalkCarry) (s : State)
    (k : Nat) (lane : Nat) (byte : UInt8) (sp fr : Nat) (e : State) : Prop where
  /-- The cursor's next entry. -/
  inc : lookupName e.env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 (k + 1)))
  /-- The entry's position. -/
  idx : lookupName e.env "%idxprom.peel" = some (.int 64 (BitVec.ofNat 64 lane))
  /-- The entry's first byte. -/
  bv : lookupName e.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat))
  /-- The frame's `phi`. -/
  frame : lookupName e.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr))
  /-- The depth's `phi`. -/
  sp : lookupName e.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp))
  /-- The term count's `phi`. -/
  terms : lookupName e.env "%terms.0.ph1407" =
    some (.int 64 (BitVec.ofNat 64 K.terms))
  /-- The token count's `phi`. -/
  tokens : lookupName e.env "%tokens.0.ph1408" =
    some (.int 64 (BitVec.ofNat 64 K.tok))
  /-- The document's base. -/
  b : lookupName e.env "%b" = some (.ptr K.b)
  /-- The entry count. -/
  nep : lookupName e.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep))
  /-- The document's length. -/
  n : lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n))
  /-- The entry stream's base. -/
  ep : lookupName e.env "%ep" = some (.ptr K.ep)
  /-- The entry chain's `%b - 1`. -/
  gep : lookupName e.env "%invariant.gep1068" = some (.ptr (K.b - 1))
  /-- The cursor record's index cell. -/
  k219 : lookupName e.env "%k219" = some (.ptr (K.c + 32))
  /-- The entry's position in the stream. -/
  ent : K.ent[k]? = some lane
  /-- The position is a lane word. -/
  laneLt : lane < 2 ^ 32
  /-- The document's byte at the position. -/
  bs : K.bs[lane]? = some byte
  /-- And the caller's memory carries it. -/
  read : readBytes s.mem (K.b + lane) 1 = some [byte]

/-- A name a cell list does not bind reads through it. -/
theorem valuePrefixFree {cells : List (String × Value)} {n : String}
    (h : n ∉ cells.map (·.1)) : ∀ w, (n, w) ∈ cells → False := by
  intro w hw
  exact h (List.mem_map.mpr ⟨(n, w), hw, rfl⟩)

/-- A name a cell list does not bind reads through it.  This is
`lookupName_cons_ne` peeled once per prepended cell, which is how a continuation
reads the entry's registers at a state it did not build. -/
theorem valueLookup_append {cells : List (String × Value)} {name : String} {v : Value}
    (env : Env) (h : ∀ w, (name, w) ∈ cells → False)
    (h0 : lookupName env name = some v) :
    lookupName (cells ++ env) name = some v := by
  induction cells with
  | nil => simpa using h0
  | cons c rest ih =>
      obtain ⟨k, w⟩ := c
      rw [List.cons_append, lookupName_cons_ne w (rest ++ env)]
      · exact ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
      · intro hk
        exact h w (by rw [hk]; exact List.mem_cons_self ..)

/-- The builder is the list append. -/
theorem cells_eq_append (cs : List (String × Value)) (env : Env) :
    cells cs env = cs ++ env := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp only [cells, List.cons_append, ih]

/-- **The `scalar` state's registers at a head's values.**  The state's
environment is the head's behind the leaf dispatch's cells, which bind none of
the head's registers. -/
theorem Stage2NoEventWalkHead.valueRegs {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s e : State} (h : Stage2NoEventWalkHead K mem k s)
    {cs : List (String × Value)} (henv : e.env = cells cs s.env)
    (hnames : cs.map (·.1) = ["%SwitchLeaf", "%Pivot6"] ∨
      cs.map (·.1) = ["%SwitchLeaf2", "%Pivot", "%Pivot6"] ∨
      cs.map (·.1) = ["%SwitchLeaf4", "%Pivot", "%Pivot6"]) :
    ∃ (lane : Nat) (byte : UInt8) (sp fr : Nat),
      Stage2NoEventWalkValueRegs K s k lane byte sp fr e := by
  obtain ⟨lane, byte, hent, hlane32, hbs, hread, -, hidx, hinc, -, -, h3⟩ := h.laneRead
  obtain ⟨sp, fr, one, wide, hsp, hfr, -, -, -, -⟩ := h.spPhi
  have hregs : Stage2NoEventWalkValueRegs K s k lane byte sp fr e := by
    refine
      { inc := ?_, idx := ?_, bv := ?_, frame := ?_, sp := ?_, terms := ?_,
        tokens := ?_, b := ?_, nep := ?_, n := ?_, ep := ?_, gep := ?_,
        k219 := ?_, ent := hent, laneLt := hlane32, bs := hbs, read := hread }
    all_goals
      rw [henv, cells_eq_append]
      refine valueLookup_append s.env (valuePrefixFree ?_) ?_
      · rcases hnames with h' | h' | h' <;> rw [h'] <;> decide
      · first
        | exact hinc
        | exact hidx
        | exact h3
        | exact hfr
        | exact hsp
        | exact h.termsPhi
        | exact h.tokensPhi
        | exact h.bLookup
        | exact h.nepLookup
        | exact h.nLookup
        | exact h.epLookup
        | exact h.gep1068Lookup
        | exact h.k219Lookup
  exact ⟨lane, byte, sp, fr, hregs⟩

/-- A two-link chain's run, at the counts' sum.  The states are parameters, so
the statement does not depend on how a route writes them. -/
theorem valueChainRunTwo {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s s1 s2 : State}
    (L1 : Stage2NoEventWalkLink calls K mem s K s1)
    (L2 : Stage2NoEventWalkLink calls K mem s1 K s2) :
    ∀ n, runFuel calls (2 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody s2 := by
  intro n
  rw [show 2 + n = 1 + (1 + n) from by omega,
    stage2NoEventWalkLink_runFuel L1 (1 + n), stage2NoEventWalkLink_runFuel L2 n]

/-- A three-link chain's run, at the counts' sum. -/
theorem valueChainRunThree {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s s1 s2 s3 : State}
    (L1 : Stage2NoEventWalkLink calls K mem s K s1)
    (L2 : Stage2NoEventWalkLink calls K mem s1 K s2)
    (L3 : Stage2NoEventWalkLink calls K mem s2 K s3) :
    ∀ n, runFuel calls (3 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody s3 := by
  intro n
  rw [show 3 + n = 1 + (1 + (1 + n)) from by omega,
    stage2NoEventWalkLink_runFuel L1 (1 + (1 + n)),
    stage2NoEventWalkLink_runFuel L2 (1 + n), stage2NoEventWalkLink_runFuel L3 n]

/-! ### The value class at a head

The head's byte is a value byte when it is none of `"`, `[`, `{`; the dispatch
then takes one of the three leaves, whose step counts are two, three and three.
Each path is its own theorem, and `stage2NoEventWalkValue` dispatches the byte to
them.  Composing the dispatch with the class's route gives the class's price at a
head: `18 + 5 * (cond - lane)` steps from `NodeBlock5` to the number or literal
entry. -/

/-- **The `LeafBlock` path**: a byte below 91 signed that is not `"`. -/
theorem stage2NoEventWalkValueLeaf {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {y : BitVec 8}
    (hhead : Stage2NoEventWalkHead K mem k s)
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy34 : y ≠ BitVec.ofNat 8 34)
    (hlt91 : y.toInt < (BitVec.ofNat 8 91).toInt)
    :
    ∃ (e' : State) (j q cond lane : Nat) (byte : UInt8),
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      j ≤ 18 + 5 * (cond - lane) ∧
      (e'.pc = "if.then471" ∨ e'.pc = "if.else495") ∧
      lookupName e'.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lane ≤ q ∧ q ≤ cond ∧ cond ≤ K.n ∧ lane < cond ∧
      (cond = K.n ∨ K.ent[k + 1]? = some cond) ∧
      (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD q 0).toNat) = true) ∧
      ((∀ j, lane ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (K.bs.getD j 0).toNat) = false) ∨
        (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD (cond - 1) 0).toNat) = false)) ∧
      Stage2NoEventWalkInv K mem e' ∧
      e'.mem = writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 1)).toNat 8) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e') := by
    have hy91' : evalICmp .slt y (BitVec.ofNat 8 91) = 1 :=
      stage2NoEvent_slt_one_of_toInt_lt hlt91
    have hy34' : evalICmp .eq y (BitVec.ofNat 8 34) = 0 :=
      stage2NoEvent_eq_zero_of_ne hy34
    have L1 := link_nodeBlock5_true (calls := calls) (K := K) (mem := mem) hhead.inv
      hhead.pc h3 hy91'
    have h31 : lookupName (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) "%3"
        = some (.int 8 y) := lookupName_cons_other s.env "%Pivot6" (.int 1 1)
      (by decide) h3
    have L2 := link_leafBlock_false (calls := calls) (K := K) (mem := mem)
      (s := stage2NoEventWalkNext (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) s
        "LeafBlock") L1.inv' rfl h31 hy34'
    obtain ⟨lane, byte, sp, fr, R⟩ := hhead.valueRegs
      (cs := [("%SwitchLeaf", .int 1 (0 : BitVec 1)),
        ("%Pivot6", .int 1 (1 : BitVec 1))])
      (e := stage2NoEventWalkNext
        (("%SwitchLeaf", .int 1 (0 : BitVec 1)) ::
          ("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env)
        (stage2NoEventWalkNext (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) s
          "LeafBlock") "scalar")
      rfl (Or.inl rfl)
    obtain ⟨e', jR, q, cond, hprice, hpc', hee, hq1, hq2, hcondN, hlanelt, hdisj, hws,
      hprefix, hinv', hmem', hrun'⟩ :=
      stage2NoEventWalkValueAt (calls := calls) (K := K) (mem := mem)
        (e := stage2NoEventWalkNext
          (("%SwitchLeaf", .int 1 (0 : BitVec 1)) ::
            ("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env)
          (stage2NoEventWalkNext (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) s
            "LeafBlock") "scalar")
        (pre := "LeafBlock") L2.inv' rfl rfl (Or.inl rfl) hhead.bPos
        R.ent R.laneLt R.inc R.idx R.bv R.frame R.sp R.terms R.tokens R.b R.nep
        R.n R.ep R.gep R.k219 hhead.klt
    have hrun2 : ∀ n, runFuel calls (2 + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody
          (stage2NoEventWalkNext
            (("%SwitchLeaf", .int 1 (0 : BitVec 1)) ::
              ("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env)
            (stage2NoEventWalkNext (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) s
              "LeafBlock") "scalar") := valueChainRunTwo L1 L2
    refine ⟨e', 2 + jR, q, cond, lane, byte, R.ent, R.laneLt, R.bs, R.read, ?_,
      hpc', hee, hq1, hq2, hcondN, hlanelt, hdisj, hws, hprefix, hinv', ?_, ?_⟩
    · omega
    · simpa only [stage2NoEventWalkNext_mem] using hmem'
    · intro n
      have h1 := hrun2 (jR + n)
      simpa only [Nat.add_assoc] using h1.trans (hrun' n)

/-- **The `LeafBlock1` path**: 91 at or below the byte, below 123 signed, not `[`. -/
theorem stage2NoEventWalkValueLeaf1 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {y : BitVec 8}
    (hhead : Stage2NoEventWalkHead K mem k s)
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy91 : y ≠ BitVec.ofNat 8 91)
    (hge91 : (BitVec.ofNat 8 91).toInt ≤ y.toInt)
    (hlt123 : y.toInt < (BitVec.ofNat 8 123).toInt)
    :
    ∃ (e' : State) (j q cond lane : Nat) (byte : UInt8),
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      j ≤ 18 + 5 * (cond - lane) ∧
      (e'.pc = "if.then471" ∨ e'.pc = "if.else495") ∧
      lookupName e'.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lane ≤ q ∧ q ≤ cond ∧ cond ≤ K.n ∧ lane < cond ∧
      (cond = K.n ∨ K.ent[k + 1]? = some cond) ∧
      (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD q 0).toNat) = true) ∧
      ((∀ j, lane ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (K.bs.getD j 0).toNat) = false) ∨
        (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD (cond - 1) 0).toNat) = false)) ∧
      Stage2NoEventWalkInv K mem e' ∧
      e'.mem = writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 1)).toNat 8) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e') := by
      have hy91' : evalICmp .slt y (BitVec.ofNat 8 91) = 0 :=
        stage2NoEvent_slt_zero_of_toInt_ge hge91
      have hy123' : evalICmp .slt y (BitVec.ofNat 8 123) = 1 :=
        stage2NoEvent_slt_one_of_toInt_lt hlt123
      have hy91eq : evalICmp .eq y (BitVec.ofNat 8 91) = 0 :=
        stage2NoEvent_eq_zero_of_ne hy91
      have L1 := link_nodeBlock5_false (calls := calls) (K := K) (mem := mem) hhead.inv
        hhead.pc h3 hy91'
      have h31 : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
          = some (.int 8 y) := lookupName_cons_other s.env "%Pivot6" (.int 1 0)
        (by decide) h3
      have L2 := link_nodeBlock_true (calls := calls) (K := K) (mem := mem)
        (s := stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
          "NodeBlock") L1.inv' rfl h31 hy123'
      have h32 : lookupName
          (("%Pivot", .int 1 (1 : BitVec 1)) ::
            ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3" = some (.int 8 y) :=
        lookupName_cons_other _ "%Pivot" (.int 1 1) (by decide) h31
      have L3 := link_leafBlock1_false (calls := calls) (K := K) (mem := mem)
        (s := stage2NoEventWalkNext
          (("%Pivot", .int 1 (1 : BitVec 1)) ::
            ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
          (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
            "NodeBlock") "LeafBlock1") L2.inv' rfl h32 hy91eq
      obtain ⟨lane, byte, sp, fr, R⟩ := hhead.valueRegs
        (cs := [("%SwitchLeaf2", .int 1 (0 : BitVec 1)),
          ("%Pivot", .int 1 (1 : BitVec 1)),
          ("%Pivot6", .int 1 (0 : BitVec 1))])
        (e := stage2NoEventWalkNext
          (("%SwitchLeaf2", .int 1 (0 : BitVec 1)) ::
            ("%Pivot", .int 1 (1 : BitVec 1)) ::
            ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
          (stage2NoEventWalkNext
            (("%Pivot", .int 1 (1 : BitVec 1)) ::
              ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
            (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
              "NodeBlock") "LeafBlock1") "scalar")
        rfl (Or.inr (Or.inl rfl))
      obtain ⟨e', jR, q, cond, hprice, hpc', hee, hq1, hq2, hcondN, hlanelt, hdisj, hws,
        hprefix, hinv', hmem', hrun'⟩ :=
        stage2NoEventWalkValueAt (calls := calls) (K := K) (mem := mem)
          (e := stage2NoEventWalkNext
            (("%SwitchLeaf2", .int 1 (0 : BitVec 1)) ::
              ("%Pivot", .int 1 (1 : BitVec 1)) ::
              ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
            (stage2NoEventWalkNext
              (("%Pivot", .int 1 (1 : BitVec 1)) ::
                ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
              (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
                "NodeBlock") "LeafBlock1") "scalar")
          (pre := "LeafBlock1") L3.inv' rfl rfl (Or.inr (Or.inl rfl)) hhead.bPos
          R.ent R.laneLt R.inc R.idx R.bv R.frame R.sp R.terms R.tokens R.b R.nep
          R.n R.ep R.gep R.k219 hhead.klt
      have hrun3 : ∀ n, runFuel calls (3 + n) stage2NoEventBody s =
          runFuel calls n stage2NoEventBody
            (stage2NoEventWalkNext
              (("%SwitchLeaf2", .int 1 (0 : BitVec 1)) ::
                ("%Pivot", .int 1 (1 : BitVec 1)) ::
                ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
              (stage2NoEventWalkNext
                (("%Pivot", .int 1 (1 : BitVec 1)) ::
                  ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
                (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
                  "NodeBlock") "LeafBlock1") "scalar") := valueChainRunThree L1 L2 L3
      refine ⟨e', 3 + jR, q, cond, lane, byte, R.ent, R.laneLt, R.bs, R.read, ?_,
        hpc', hee, hq1, hq2, hcondN, hlanelt, hdisj, hws, hprefix, hinv', ?_, ?_⟩
      · omega
      · simpa only [stage2NoEventWalkNext_mem] using hmem'
      · intro n
        have h1 := hrun3 (jR + n)
        simpa only [Nat.add_assoc] using h1.trans (hrun' n)

/-- **The `LeafBlock3` path**: a byte at or above 123 signed that is not `{`. -/
theorem stage2NoEventWalkValueLeaf3 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {y : BitVec 8}
    (hhead : Stage2NoEventWalkHead K mem k s)
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy123 : y ≠ BitVec.ofNat 8 123)
    (hge91 : (BitVec.ofNat 8 91).toInt ≤ y.toInt)
    (hge123 : (BitVec.ofNat 8 123).toInt ≤ y.toInt)
    :
    ∃ (e' : State) (j q cond lane : Nat) (byte : UInt8),
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      j ≤ 18 + 5 * (cond - lane) ∧
      (e'.pc = "if.then471" ∨ e'.pc = "if.else495") ∧
      lookupName e'.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lane ≤ q ∧ q ≤ cond ∧ cond ≤ K.n ∧ lane < cond ∧
      (cond = K.n ∨ K.ent[k + 1]? = some cond) ∧
      (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD q 0).toNat) = true) ∧
      ((∀ j, lane ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (K.bs.getD j 0).toNat) = false) ∨
        (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD (cond - 1) 0).toNat) = false)) ∧
      Stage2NoEventWalkInv K mem e' ∧
      e'.mem = writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 1)).toNat 8) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e') := by
      have hy91' : evalICmp .slt y (BitVec.ofNat 8 91) = 0 :=
        stage2NoEvent_slt_zero_of_toInt_ge hge91
      have hy123' : evalICmp .slt y (BitVec.ofNat 8 123) = 0 :=
        stage2NoEvent_slt_zero_of_toInt_ge hge123
      have hy123eq : evalICmp .eq y (BitVec.ofNat 8 123) = 0 :=
        stage2NoEvent_eq_zero_of_ne hy123
      have L1 := link_nodeBlock5_false (calls := calls) (K := K) (mem := mem) hhead.inv
        hhead.pc h3 hy91'
      have h31 : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
          = some (.int 8 y) := lookupName_cons_other s.env "%Pivot6" (.int 1 0)
        (by decide) h3
      have L2 := link_nodeBlock_false (calls := calls) (K := K) (mem := mem)
        (s := stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
          "NodeBlock") L1.inv' rfl h31 hy123'
      have h32 : lookupName
          (("%Pivot", .int 1 (0 : BitVec 1)) ::
            ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3" = some (.int 8 y) :=
        lookupName_cons_other _ "%Pivot" (.int 1 0) (by decide) h31
      have L3 := link_leafBlock3_false (calls := calls) (K := K) (mem := mem)
        (s := stage2NoEventWalkNext
          (("%Pivot", .int 1 (0 : BitVec 1)) ::
            ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
          (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
            "NodeBlock") "LeafBlock3") L2.inv' rfl h32 hy123eq
      obtain ⟨lane, byte, sp, fr, R⟩ := hhead.valueRegs
        (cs := [("%SwitchLeaf4", .int 1 (0 : BitVec 1)),
          ("%Pivot", .int 1 (0 : BitVec 1)),
          ("%Pivot6", .int 1 (0 : BitVec 1))])
        (e := stage2NoEventWalkNext
          (("%SwitchLeaf4", .int 1 (0 : BitVec 1)) ::
            ("%Pivot", .int 1 (0 : BitVec 1)) ::
            ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
          (stage2NoEventWalkNext
            (("%Pivot", .int 1 (0 : BitVec 1)) ::
              ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
            (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
              "NodeBlock") "LeafBlock3") "scalar")
        rfl (Or.inr (Or.inr rfl))
      obtain ⟨e', jR, q, cond, hprice, hpc', hee, hq1, hq2, hcondN, hlanelt, hdisj, hws,
        hprefix, hinv', hmem', hrun'⟩ :=
        stage2NoEventWalkValueAt (calls := calls) (K := K) (mem := mem)
          (e := stage2NoEventWalkNext
            (("%SwitchLeaf4", .int 1 (0 : BitVec 1)) ::
              ("%Pivot", .int 1 (0 : BitVec 1)) ::
              ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
            (stage2NoEventWalkNext
              (("%Pivot", .int 1 (0 : BitVec 1)) ::
                ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
              (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
                "NodeBlock") "LeafBlock3") "scalar")
          (pre := "LeafBlock3") L3.inv' rfl rfl (Or.inr (Or.inr rfl)) hhead.bPos
          R.ent R.laneLt R.inc R.idx R.bv R.frame R.sp R.terms R.tokens R.b R.nep
          R.n R.ep R.gep R.k219 hhead.klt
      have hrun3 : ∀ n, runFuel calls (3 + n) stage2NoEventBody s =
          runFuel calls n stage2NoEventBody
            (stage2NoEventWalkNext
              (("%SwitchLeaf4", .int 1 (0 : BitVec 1)) ::
                ("%Pivot", .int 1 (0 : BitVec 1)) ::
                ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
              (stage2NoEventWalkNext
                (("%Pivot", .int 1 (0 : BitVec 1)) ::
                  ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env)
                (stage2NoEventWalkNext (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) s
                  "NodeBlock") "LeafBlock3") "scalar") := valueChainRunThree L1 L2 L3
      refine ⟨e', 3 + jR, q, cond, lane, byte, R.ent, R.laneLt, R.bs, R.read, ?_,
        hpc', hee, hq1, hq2, hcondN, hlanelt, hdisj, hws, hprefix, hinv', ?_, ?_⟩
      · omega
      · simpa only [stage2NoEventWalkNext_mem] using hmem'
      · intro n
        have h1 := hrun3 (jR + n)
        simpa only [Nat.add_assoc] using h1.trans (hrun' n)

/-- **The value class at a head**: `NodeBlock5`'s value arm to the number or
literal entry, with the scan's bound and its price.  `cond` is the next entry's
position or the document's length, `%ee.1` the scan's stop inside
`[lane, cond]`, the scan's non-membership prefix, and the run's step count is at
most `18 + 5 * (cond - lane)`. -/
theorem stage2NoEventWalkValue {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {y : BitVec 8}
    (hhead : Stage2NoEventWalkHead K mem k s)
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy34 : y ≠ BitVec.ofNat 8 34) (hy91 : y ≠ BitVec.ofNat 8 91)
    (hy123 : y ≠ BitVec.ofNat 8 123) :
    ∃ (e' : State) (j q cond lane : Nat) (byte : UInt8),
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      j ≤ 18 + 5 * (cond - lane) ∧
      (e'.pc = "if.then471" ∨ e'.pc = "if.else495") ∧
      lookupName e'.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lane ≤ q ∧ q ≤ cond ∧ cond ≤ K.n ∧ lane < cond ∧
      (cond = K.n ∨ K.ent[k + 1]? = some cond) ∧
      (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD q 0).toNat) = true) ∧
      ((∀ j, lane ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (K.bs.getD j 0).toNat) = false) ∨
        (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 (K.bs.getD (cond - 1) 0).toNat) = false)) ∧
      Stage2NoEventWalkInv K mem e' ∧
      e'.mem = writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 1)).toNat 8) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e') := by
  rcases lt_or_ge y.toInt (BitVec.ofNat 8 91).toInt with hlt91 | hge91
  · exact stage2NoEventWalkValueLeaf hhead h3 hy34 hlt91
  · rcases lt_or_ge y.toInt (BitVec.ofNat 8 123).toInt with hlt123 | hge123
    · exact stage2NoEventWalkValueLeaf1 hhead h3 hy91 hge91 hlt123
    · exact stage2NoEventWalkValueLeaf3 hhead h3 hy123 hge91 hge123

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkHead.bLookup
#print axioms Stage2NoEventWalkHead.laneAt
#print axioms Stage2NoEventWalkInv.docAt
#print axioms Stage2NoEventWalkInv.entriesAt
#print axioms Stage2NoEventWalkInv.nepLe
#print axioms Stage2NoEventWalkInv.nLt63
#print axioms valueScalar_denote
#print axioms link_valueScalar_true
#print axioms link_valueScalar_false
#print axioms stage2NoEventWalkValueAt
#print axioms Stage2NoEventWalkHead.valueRegs
#print axioms stage2NoEventWalkValue
#print axioms stage2NoEventWalkValueLeaf
#print axioms stage2NoEventWalkValueLeaf1
#print axioms stage2NoEventWalkValueLeaf3
#print axioms valueChainRunTwo
#print axioms valueChainRunThree
#print axioms Stage2NoEventWalkValueRegs.inc
#print axioms valueEnt_length_le
#print axioms valueLookup_append
#print axioms cells_eq_append

end LeanLLVM.Refinement
