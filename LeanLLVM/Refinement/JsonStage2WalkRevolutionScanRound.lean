/-
The extra-token scan's round, without a guard hypothesis.

The deleted composite `walkScanRounds457` (`JsonStage2WalkInduce`) took three `∀`-form
hypotheses at the
latch: `hround` (the visit's own segment), `hguard` (`ScanGuard` at the state's local
fact) and `hbyte` (the input's totality at the visited index).  This module shows that
the first is a theorem of the visit's own premises — the counter's two cells, the visited
byte's read and the three local facts — and that the guard is not needed to prove it: the
visit's `i + 1 < c` is a premise of the round, and the round's proof never reads
the guard the composite accepted.

**`ScanGuard` is not a fact about the walk.**  It quantifies over every pair of naturals
whose words are the two registers' and whose difference is inside the inner budget; with
the counter above the word's width the subtraction saturates at zero, so the quantified
pair always exists and the claim `i + 1 < c` is false at any state whose registers hold
words at all.  A row that carries it is uninhabited, and a producer that assumes it
assumes nothing about the run.  The `∀`-form the traversal actually needs is the round's,
stated at the state's own cells and below the word's width — `scanRoundField` — and that
is what the bundles carry.

The fields are stated at a bound the caller names, `nb`, and the round takes the bound
below `2 ^ 64` as a premise.  A bundle's bound is the lane word's `v.toNat`, so the width
is `v.isLt`'s and no row supplies it.
-/
import LeanLLVM.Refinement.JsonStage2WalkInduce

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The document's byte at `p`: the byte every visit of the whitespace skip loads. -/
def wsByte {m0 : Mem} (G : WalkGeom m0) (p : Nat) : UInt8 := G.bs.getD p 0

/-- The byte's register value, as `land.rhs.i` binds `%36`. -/
def wsX {m0 : Mem} (G : WalkGeom m0) (p : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (wsByte G p).toNat

/-- **One round of the extra-token scan, from the visit's own premises.**  The latch's
visit — one step — and the dispatch's three links: four steps.  This is
the deleted `walkScanRound457` without its guard argument, which its proof did not read: the
counter's increment being short of the bound is `hlt`, a premise, and the local fact the
visit leaves is the latch's witness `⟨i + 1, c, …, hlt, …⟩` rather than a consequence of
`ScanCount`. -/
theorem scanRound_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body462.i")
    {i c : Nat} (hi : lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hlt : i + 1 < c) (hposi : i + 1 < 2 ^ 63)
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
    ∃ (C' : WalkCarry G) (s' : State) (n : Nat),
      WalkSegment calls G C s C' s' n ∧ WalkInv G C' s' ∧ C'.block = "while.body462.i" ∧
      n ≤ stage2ByteAllowance ∧
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
  have hSC : ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.extraToken hblock] at h
  have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
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
    exact Or.inl ⟨i + 1, c, by show c - (i + 1) ≤ C.inner; omega, hlt, hcw,
      hpre, hincCell, hcondCell⟩
  obtain ⟨C₁, s₁, hC₁, hs₁, hseg₁, hb₁, hi₁, hc₁⟩ :=
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
  refine ⟨{ ScanCLand C with block := "while.body462.i" }, s₃, 1 + 3,
    hseg₁.trans hseg₃, hseg₃.inv', ?_, ?_, ?_, ?_⟩
  · simp only [ScanCLand]
  · simp [stage2ByteAllowance]
  · rw [hs₃]
    exact latch462S_counter (m0 := m0) s i c (BitVec.ofNat 64 (i + 1)) a q x
  · rw [hs₃]
    exact latch462S_cond (m0 := m0) s i c (BitVec.ofNat 64 (i + 1)) a q x hc

/-- **The traversal's round, as a row field.**  `walkScanRounds457_of_cell`'s `hround` at a named
bound `nb`: at every invariant-carrying latch state, a visit at the state's own counter
and bound, with the byte its landing loads, is a segment of at most one byte allowance
that returns to the latch with the counter advanced and the bound kept.  It is
`scanRound_at` at `nb`, and no hypothesis on the state's guard enters. -/
theorem scanRoundField {m0 : Mem} (G : WalkGeom m0) (nb : Nat)
    (hnb : nb < 2 ^ 64) :
    ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
      (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 nb)) →
      p + 1 < nb → p + 1 < 2 ^ 63 →
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
        "land.rhs457.i").env "%3" = some (.ptr a) →
      readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) →
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
        WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
        lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
        lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 nb)) :=
  fun C' s' p a bs q x hInv hblock hi hc hlt hposi h3 hread hbs h47 hbit hws hl105 hl96 hll =>
    scanRound_at (calls := stage2Calls stage2SubCalls) (G := G) (C := C') (s := s') hInv hblock
      hi hc hnb hlt hposi h3 hread hbs hl105 h47 hbit hws hl96 hll

/-- **The traversal's byte, from the document and the invariant.**  `walkScanRounds457_of_cell`'s
`hbyte` has three ingredients: the landing's address and read, the register the landing
loads, and the visited byte's class.  Only the last is the input's.  The address is
`WalkPtrs`'s `%3 = G.b` at every invariant-carrying state; the read is `walkDoc_byte`'s,
since the document lies outside the run's frame at every carry; the loaded register is
`landRhs457OutAt`'s own cell, `%47 = ofNat 8 q`; and the three local facts are `True` at
the two blocks the landing and the pivot leave and the latch's `ScanCount` at the next
counter, produced by the same witnesses the round uses.

What remains supplied is `hcls`: the visited byte's two class bits, at `wsByte G (p + 1)`
— the document's content, which no invariant clause and no callee contract fixes.  Its
range is the scan's: `st < p + 1` is the visits' lower bound, so the row says nothing
about the entry's token prefix, which the whitespace bundle's own class field makes
non-whitespace.  The bound below `G.n` is the span's,
`v.toNat ≤ entryPos G (C.k + 1) < G.n`. -/
theorem scanByteField {m0 : Mem} (G : WalkGeom m0) (nb : Nat) (hnb : nb < 2 ^ 64)
    (hn : nb ≤ G.n) (st : Nat)
    (hcls : ∀ p, st < p + 1 → p + 1 < nb →
      evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
      C'.block = "while.body462.i" → st < p + 1 → p + 1 < nb →
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 nb)) →
      ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
        lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
          "land.rhs457.i").env "%3" = some (.ptr a) ∧
        readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
        evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
        evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
        WalkLocal (ScanC₁₀₅ (ScanCLand C'))
          (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
            "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
        WalkLocal (ScanC₉₆ (ScanCLand C'))
          (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x) ∧
        WalkLocal { ScanCLand C' with block := "while.body462.i" }
          (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x) := by
  intro C' s' p hInv' hblock' hlo hlt hi hc
  -- the address: `%3` is the document's base at every invariant-carrying state
  have h3 : lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
      "land.rhs457.i").env "%3" = some (.ptr G.b) := by
    simp only [scanLatchOut, stateAt, cells,
      lookupName_cons_ne (k := "%exitcond298.not") (n := "%3") _ _ (by decide),
      lookupName_cons_ne (k := "%inc463.i") (n := "%3") _ _ (by decide)]
    exact hInv'.ptrs.1
  -- the read: the document's floor is outside the run's frame
  have hread : readBytes s'.mem (G.b + (p + 1)) 1 = some [wsByte G (p + 1)] := by
    have halen : C'.alen ≤ G.ndst0 + G.n + stage2ArenaReserve := by
      have := hInv'.alen_le; omega
    have hevlen : C'.evlen ≤ G.evcap := le_trans hInv'.evlen_le G.evRoom
    have hq : p + 1 < G.n := by omega
    simpa only [wsByte] using walkDoc_byte G C' s' hInv' halen hevlen hq
  -- the register: the landing's own cell, at the byte it loaded
  have h47 : evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not"
      p nb "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) G.b (wsByte G (p + 1)).toNat)
      (.reg "%47") = some (.int 8 (wsX G (p + 1))) := by
    simp only [landRhs457OutAt, stateAt, cells, evalOperand, lookupName_cons_self, wsX]
  -- the two blocks the landing and the pivot leave carry no local fact
  have hl105 : WalkLocal (ScanC₁₀₅ (ScanCLand C'))
      (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) G.b (wsByte G (p + 1)).toNat) := by
    simp [WalkLocal, ScanC₁₀₅, ScanCLand]
  have hl96 : WalkLocal (ScanC₉₆ (ScanCLand C'))
      (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) G.b (wsByte G (p + 1)).toNat (wsX G (p + 1))) := by
    simp [WalkLocal, ScanC₉₆, ScanC₁₀₅, ScanCLand]
  -- the latch's own `ScanCount`, at the incremented counter and the kept bound
  have hlatch : WalkLocal { ScanCLand C' with block := "while.body462.i" }
      (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p nb "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) G.b (wsByte G (p + 1)).toNat (wsX G (p + 1))) := by
    rw [WalkLocal.extraToken rfl]
    have hSC : ScanCount s' "%q.0.i246" "%cond350.i" C'.inner := by
      have h := hInv'.blockLocal
      rwa [WalkLocal.extraToken hblock'] at h
    have hsub : nb - p ≤ C'.inner := ScanCount.same hSC hi hc hnb (by omega)
    have hsub' : nb - (p + 1) ≤ C'.inner :=
      le_trans (Nat.sub_le_sub_left (by omega : p ≤ p + 1) nb) hsub
    exact ⟨p + 1, nb, hsub', hlt, hnb,
      latch462S_counter (m0 := m0) s' p nb (BitVec.ofNat 64 (p + 1)) G.b
        (wsByte G (p + 1)).toNat (wsX G (p + 1)),
      latch462S_cond (m0 := m0) s' p nb (BitVec.ofNat 64 (p + 1)) G.b
        (wsByte G (p + 1)).toNat (wsX G (p + 1)) hc⟩
  obtain ⟨hb, hw⟩ := hcls p hlo hlt
  exact ⟨G.b, [wsByte G (p + 1)], (wsByte G (p + 1)).toNat, wsX G (p + 1),
    h3, hread, bytesToNat_singleton _, h47, hb, hw, hl105, hl96, hlatch⟩

/-- **The extra-token scan's visits, composed, without a guard hypothesis.**

This is the deleted `walkScanRounds457` with its `hguard` parameter **dropped, not restated**: the
induction never reads it.  `go`'s base case needs nothing but the counter's cell, and its
step gets `i + 1 < c` from `c - 1 - i = r + 1` and `i < c` — the decomposition of the
remaining distance, not the guard — then applies `hround` at that visit.  The guard's only
appearance in the original is as an argument forwarded to the recursive hypothesis, so the
whole parameter is dead weight; `walkScanArrival457_of_cell` below drops it there too.

The two hypotheses are the round at a given byte (`hround`, produced by `scanRoundField`)
and the input's totality at every index the scan visits (`hbyte`, whose read is
`scanByteField`'s and whose two class bits are the document's).  Neither is a
`ScanGuard`: that predicate quantifies over every natural pair carrying the two register
words, so above the word's width the saturating subtraction admits pairs that refute it,
and it is false at any state whose registers hold words. -/
theorem walkScanRounds457_of_cell {calls : Calls} {m0 : Mem} (G : WalkGeom m0) {i c : Nat}
    (hround : ∀ (C : WalkCarry G) (s : State) (p a : Nat) (bs : List UInt8) (q : Nat)
      (x : BitVec 8), WalkInv G C s → C.block = "while.body462.i" →
      lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      p + 1 < c → p + 1 < 2 ^ 63 →
      lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i").env
        "%3" = some (.ptr a) →
      readBytes s.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
      evalOperand (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" p c
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
      WalkLocal (ScanC₁₀₅ (ScanCLand C))
        (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q) →
      WalkLocal (ScanC₉₆ (ScanCLand C))
        (ScanS₉₆ (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      WalkLocal { ScanCLand C with block := "while.body462.i" }
        (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      ∃ (C' : WalkCarry G) (s' : State) (j : Nat), WalkSegment calls G C s C' s' j ∧
        WalkInv G C' s' ∧ C'.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
        lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
        lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hbyte : ∀ (C : WalkCarry G) (s : State) (p : Nat), WalkInv G C s →
      C.block = "while.body462.i" → i < p + 1 → p + 1 < c →
      lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
        lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i").env
          "%3" = some (.ptr a) ∧
        readBytes s.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
        evalOperand (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" p c
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
        evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
        WalkLocal (ScanC₁₀₅ (ScanCLand C))
          (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q) ∧
        WalkLocal (ScanC₉₆ (ScanCLand C))
          (ScanS₉₆ (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x) ∧
        WalkLocal { ScanCLand C with block := "while.body462.i" }
          (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x))
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "while.body462.i")
    (hi : lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hc63 : c ≤ 2 ^ 63) (hic : i < c) :
    ∃ (C' : WalkCarry G) (s' : State) (n : Nat),
      WalkSegment calls G C s C' s' n ∧ WalkInv G C' s' ∧ C'.block = "while.body462.i" ∧
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (c - 1))) ∧
      n ≤ stage2ByteAllowance * (c - 1 - i) := by
  have go : ∀ r, ∀ (j : Nat) (C : WalkCarry G) (s : State), c - 1 - j = r →
      WalkInv G C s → C.block = "while.body462.i" →
      lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 j)) →
      lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      j < c → i ≤ j →
      ∃ (C' : WalkCarry G) (s' : State) (n : Nat),
        WalkSegment calls G C s C' s' n ∧ WalkInv G C' s' ∧ C'.block = "while.body462.i" ∧
        lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (c - 1))) ∧
        n ≤ stage2ByteAllowance * r := by
    intro r
    induction r with
    | zero =>
        intro j C s _ hInv hblock hi _ hic _
        have hie : j = c - 1 := by omega
        exact ⟨C, s, 0, Seg.measure (Seg.nil hInv), hInv, hblock, by rw [← hie]; exact hi, by simp⟩
    | succ n ih =>
        intro j C s hr hInv hblock hi hc' hic hlo
        have hlt : j + 1 < c := by omega
        have hposi : j + 1 < 2 ^ 63 := by omega
        obtain ⟨a, bs, q, x, h3, hread, hbs, h47, hbit, hws, hl105, hl96, hll⟩ :=
          hbyte C s j hInv hblock (by omega) hlt hi hc'
        obtain ⟨C₁, s₁, j₁, hseg, hInv₁, hb₁, hj, hi₁, hc₁⟩ :=
          hround C s j a bs q x hInv hblock hi hc' hlt hposi h3 hread hbs h47 hbit hws
            hl105 hl96 hll
        obtain ⟨C₂, s₂, m, hseg₂, hInv₂, hb₂, hi₂, hm⟩ :=
          ih (j + 1) C₁ s₁ (by omega) hInv₁ hb₁ hi₁ hc₁ (by omega) (by omega)
        refine ⟨C₂, s₂, j₁ + m, hseg.trans hseg₂, hInv₂, hb₂, hi₂, ?_⟩
        rw [Nat.mul_succ]
        omega
  obtain ⟨C', s', n, hseg, hInv', hb, hi', hn⟩ :=
    go (c - 1 - i) i C s rfl hInv hblock hi hc hic (le_rfl)
  exact ⟨C', s', n, hseg, hInv', hb, hi', hn⟩

/-- **The scan's arrival at its last visit, without a guard hypothesis.**  The visit
traversal above, with the round built by `scanRound_at` — the guard-free round — rather
than by the deleted `walkScanRound457`, which still took a `ScanGuard` its proof did not
read. -/
theorem walkScanArrival457_of_cell {calls : Calls} {m0 : Mem} (G : WalkGeom m0) {i c : Nat}
    (hbyte : ∀ (C : WalkCarry G) (s : State) (p : Nat), WalkInv G C s →
      C.block = "while.body462.i" → i < p + 1 → p + 1 < c →
      lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
        lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i").env
          "%3" = some (.ptr a) ∧
        readBytes s.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
        evalOperand (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" p c
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
        evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
        WalkLocal (ScanC₁₀₅ (ScanCLand C))
          (landRhs457OutAt (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q) ∧
        WalkLocal (ScanC₉₆ (ScanCLand C))
          (ScanS₉₆ (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x) ∧
        WalkLocal { ScanCLand C with block := "while.body462.i" }
          (Latch462S (scanLatchOut s "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x))
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "while.body462.i")
    (hi : lookupName s.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hc63 : c ≤ 2 ^ 63) (hic : i < c) :
    ∃ (C' : WalkCarry G) (s' : State) (n : Nat),
      WalkSegment calls G C s C' s' n ∧ WalkInv G C' s' ∧ C'.block = "while.body462.i" ∧
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (c - 1))) ∧
      n ≤ stage2ByteAllowance * (c - 1 - i) :=
  walkScanRounds457_of_cell (calls := calls) G
    (hround := by
      intro C₀ s₀ p a bs q x hInv₀ hblock₀ hi₀ hc₀ hlt hposi h3 hread hbs h47 hbit hws
        hl105 hl96 hll
      exact scanRound_at (calls := calls) (G := G) (C := C₀) (s := s₀) hInv₀ hblock₀
        hi₀ hc₀ hcw hlt hposi h3 hread hbs hl105 h47 hbit hws hl96 hll)
    hbyte hInv hblock hi hc hcw hc63 hic

/-- **The token record's register at every invariant-carrying latch state**, as a row
field: `%t352.i` is one of `walkStaticRegs`, so the invariant's `regs` clause carries it
at every state.  The traversal's own endpoint is existential, but the field quantifies
over the invariant's states rather than over that endpoint, which is why no preservation
lemma is needed. -/
theorem scanTokField {m0 : Mem} (G : WalkGeom m0) :
    ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
      C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok) :=
  fun C' _ hInv' _ =>
    ⟨C'.stage.tok, hInv'.regs ("%t352.i", .ptr C'.stage.tok) (by simp [walkStaticRegs])⟩

end WalkScope

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scanRound_at
#print axioms LeanLLVM.Refinement.WalkScope.scanRoundField
#print axioms LeanLLVM.Refinement.WalkScope.scanByteField
#print axioms LeanLLVM.Refinement.WalkScope.scanTokField
#print axioms LeanLLVM.Refinement.WalkScope.walkScanRounds457_of_cell
#print axioms LeanLLVM.Refinement.WalkScope.walkScanArrival457_of_cell

end LeanLLVM.Refinement
